//! Flat Tag-Based URN Identifier System
//!
//! This module provides a flat, tag-based tagged URN system with configurable
//! prefixes, wildcard support, and specificity comparison.

use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::collections::BTreeMap;
use std::fmt;
use std::str::FromStr;

/// A tagged URN using flat, ordered tags with a configurable prefix
///
/// Examples:
/// - `cap:op=generate;ext=pdf;output=binary;target=thumbnail`
/// - `myapp:key="Value With Spaces"`
/// - `custom:a=1;b=2`
#[derive(Debug, Clone, Eq, Hash)]
pub struct TaggedUrn {
    /// The prefix for this URN (e.g., "cap", "myapp", "custom")
    pub prefix: String,
    /// The tags that define this URN, stored in sorted order for canonical representation
    pub tags: BTreeMap<String, String>,
}

impl PartialEq for TaggedUrn {
    fn eq(&self, other: &Self) -> bool {
        self.prefix == other.prefix && self.tags == other.tags
    }
}

/// Parser states for the state machine
#[derive(Debug, Clone, Copy, PartialEq)]
enum ParseState {
    ExpectingKey,
    InKey,
    ExpectingValue,
    InUnquotedValue,
    InQuotedValue,
    InQuotedValueEscape,
    ExpectingSemiOrEnd,
}

impl TaggedUrn {
    /// Create a new tagged URN from tags with a specified prefix
    /// Keys are normalized to lowercase; values are preserved as-is
    pub fn new(prefix: String, tags: BTreeMap<String, String>) -> Self {
        let normalized_tags = tags
            .into_iter()
            .map(|(k, v)| (k.to_lowercase(), v))
            .collect();
        Self {
            prefix: prefix.to_lowercase(),
            tags: normalized_tags,
        }
    }

    /// Create an empty tagged URN with the specified prefix
    pub fn empty(prefix: String) -> Self {
        Self {
            prefix: prefix.to_lowercase(),
            tags: BTreeMap::new(),
        }
    }

    /// Create a tagged URN from a string representation
    ///
    /// Format: `prefix:key1=value1;key2=value2;...` or `prefix:key1="value with spaces";key2=simple`
    /// The prefix is required and ends at the first colon
    /// Trailing semicolons are optional and ignored
    /// Tags are automatically sorted alphabetically for canonical form
    ///
    /// Case handling:
    /// - Prefix: Normalized to lowercase
    /// - Keys: Always normalized to lowercase
    /// - Unquoted values: Normalized to lowercase
    /// - Quoted values: Case preserved exactly as specified
    pub fn from_string(s: &str) -> Result<Self, TaggedUrnError> {
        // Fail hard on leading/trailing whitespace
        if s != s.trim() {
            return Err(TaggedUrnError::WhitespaceInInput(s.to_string()));
        }

        if s.is_empty() {
            return Err(TaggedUrnError::Empty);
        }

        // Find the prefix (everything before the first colon)
        let colon_pos = s.find(':').ok_or(TaggedUrnError::MissingPrefix)?;

        if colon_pos == 0 {
            return Err(TaggedUrnError::EmptyPrefix);
        }

        let prefix = s[..colon_pos].to_lowercase();
        let tags_part = &s[colon_pos + 1..];
        let mut tags = BTreeMap::new();

        // Handle empty tagged URN (prefix: with no tags)
        if tags_part.is_empty() || tags_part == ";" {
            return Ok(Self { prefix, tags });
        }

        let mut state = ParseState::ExpectingKey;
        let mut current_key = String::new();
        let mut current_value = String::new();
        let chars: Vec<char> = tags_part.chars().collect();
        let mut pos = 0;

        while pos < chars.len() {
            let c = chars[pos];

            match state {
                ParseState::ExpectingKey => {
                    if c == ';' {
                        // Empty segment, skip
                        pos += 1;
                        continue;
                    } else if Self::is_valid_key_char(c) {
                        current_key.push(c.to_ascii_lowercase());
                        state = ParseState::InKey;
                    } else {
                        return Err(TaggedUrnError::InvalidCharacter(format!(
                            "invalid character '{}' at position {}",
                            c, pos
                        )));
                    }
                }

                ParseState::InKey => {
                    if c == '=' {
                        if current_key.is_empty() {
                            return Err(TaggedUrnError::EmptyTagComponent(
                                "empty key".to_string(),
                            ));
                        }
                        state = ParseState::ExpectingValue;
                    } else if c == ';' {
                        // Value-less tag: treat as wildcard
                        if current_key.is_empty() {
                            return Err(TaggedUrnError::EmptyTagComponent(
                                "empty key".to_string(),
                            ));
                        }
                        current_value = "*".to_string();
                        Self::finish_tag(&mut tags, &mut current_key, &mut current_value)?;
                        state = ParseState::ExpectingKey;
                    } else if Self::is_valid_key_char(c) {
                        current_key.push(c.to_ascii_lowercase());
                    } else {
                        return Err(TaggedUrnError::InvalidCharacter(format!(
                            "invalid character '{}' in key at position {}",
                            c, pos
                        )));
                    }
                }

                ParseState::ExpectingValue => {
                    if c == '"' {
                        state = ParseState::InQuotedValue;
                    } else if c == ';' {
                        return Err(TaggedUrnError::EmptyTagComponent(format!(
                            "empty value for key '{}'",
                            current_key
                        )));
                    } else if Self::is_valid_unquoted_value_char(c) {
                        current_value.push(c.to_ascii_lowercase());
                        state = ParseState::InUnquotedValue;
                    } else {
                        return Err(TaggedUrnError::InvalidCharacter(format!(
                            "invalid character '{}' in value at position {}",
                            c, pos
                        )));
                    }
                }

                ParseState::InUnquotedValue => {
                    if c == ';' {
                        Self::finish_tag(&mut tags, &mut current_key, &mut current_value)?;
                        state = ParseState::ExpectingKey;
                    } else if Self::is_valid_unquoted_value_char(c) {
                        current_value.push(c.to_ascii_lowercase());
                    } else {
                        return Err(TaggedUrnError::InvalidCharacter(format!(
                            "invalid character '{}' in unquoted value at position {}",
                            c, pos
                        )));
                    }
                }

                ParseState::InQuotedValue => {
                    if c == '"' {
                        state = ParseState::ExpectingSemiOrEnd;
                    } else if c == '\\' {
                        state = ParseState::InQuotedValueEscape;
                    } else {
                        // Any character allowed in quoted value, preserve case
                        current_value.push(c);
                    }
                }

                ParseState::InQuotedValueEscape => {
                    if c == '"' || c == '\\' {
                        current_value.push(c);
                        state = ParseState::InQuotedValue;
                    } else {
                        return Err(TaggedUrnError::InvalidEscapeSequence(pos));
                    }
                }

                ParseState::ExpectingSemiOrEnd => {
                    if c == ';' {
                        Self::finish_tag(&mut tags, &mut current_key, &mut current_value)?;
                        state = ParseState::ExpectingKey;
                    } else {
                        return Err(TaggedUrnError::InvalidCharacter(format!(
                            "expected ';' or end after quoted value, got '{}' at position {}",
                            c, pos
                        )));
                    }
                }
            }

            pos += 1;
        }

        // Handle end of input
        match state {
            ParseState::InUnquotedValue | ParseState::ExpectingSemiOrEnd => {
                Self::finish_tag(&mut tags, &mut current_key, &mut current_value)?;
            }
            ParseState::ExpectingKey => {
                // Valid - trailing semicolon or empty input after prefix
            }
            ParseState::InQuotedValue | ParseState::InQuotedValueEscape => {
                return Err(TaggedUrnError::UnterminatedQuote(pos));
            }
            ParseState::InKey => {
                // Value-less tag at end: treat as wildcard
                if current_key.is_empty() {
                    return Err(TaggedUrnError::EmptyTagComponent(
                        "empty key".to_string(),
                    ));
                }
                current_value = "*".to_string();
                Self::finish_tag(&mut tags, &mut current_key, &mut current_value)?;
            }
            ParseState::ExpectingValue => {
                return Err(TaggedUrnError::EmptyTagComponent(format!(
                    "empty value for key '{}'",
                    current_key
                )));
            }
        }

        Ok(Self { prefix, tags })
    }

    /// Finish a tag by validating and inserting it
    fn finish_tag(
        tags: &mut BTreeMap<String, String>,
        key: &mut String,
        value: &mut String,
    ) -> Result<(), TaggedUrnError> {
        if key.is_empty() {
            return Err(TaggedUrnError::EmptyTagComponent("empty key".to_string()));
        }
        if value.is_empty() {
            return Err(TaggedUrnError::EmptyTagComponent(format!(
                "empty value for key '{}'",
                key
            )));
        }

        // Check for duplicate keys
        if tags.contains_key(key.as_str()) {
            return Err(TaggedUrnError::DuplicateKey(key.clone()));
        }

        // Validate key cannot be purely numeric
        if Self::is_purely_numeric(key) {
            return Err(TaggedUrnError::NumericKey(key.clone()));
        }

        tags.insert(std::mem::take(key), std::mem::take(value));
        Ok(())
    }

    /// Check if character is valid for a key
    fn is_valid_key_char(c: char) -> bool {
        c.is_alphanumeric() || c == '_' || c == '-' || c == '/' || c == ':' || c == '.'
    }

    /// Check if character is valid for an unquoted value
    fn is_valid_unquoted_value_char(c: char) -> bool {
        c.is_alphanumeric()
            || c == '_'
            || c == '-'
            || c == '/'
            || c == ':'
            || c == '.'
            || c == '*'
            || c == '?'
            || c == '!'
    }

    /// Check if a string is purely numeric
    fn is_purely_numeric(s: &str) -> bool {
        !s.is_empty() && s.chars().all(|c| c.is_ascii_digit())
    }

    /// Check if a value needs quoting for serialization
    fn needs_quoting(value: &str) -> bool {
        value.chars().any(|c| {
            c == ';' || c == '=' || c == '"' || c == '\\' || c == ' ' || c.is_uppercase()
        })
    }

    /// Quote a value for serialization
    fn quote_value(value: &str) -> String {
        let mut result = String::with_capacity(value.len() + 2);
        result.push('"');
        for c in value.chars() {
            if c == '"' || c == '\\' {
                result.push('\\');
            }
            result.push(c);
        }
        result.push('"');
        result
    }

    /// Get the canonical string representation of this tagged URN
    ///
    /// Uses the stored prefix
    /// Tags are already sorted alphabetically due to BTreeMap
    /// No trailing semicolon in canonical form
    /// Values are quoted only when necessary (smart quoting)
    /// Special value serialization:
    /// - `*` (must-have-any): serialized as value-less tag (just the key)
    /// - `?` (unspecified): serialized as key=?
    /// - `!` (must-not-have): serialized as key=!
    /// Serialize just the tags portion (without prefix)
    ///
    /// Returns the tags in canonical form with proper quoting and sorting.
    /// This is the portion after the ":" in a full URN string.
    pub fn tags_to_string(&self) -> String {
        self
            .tags
            .iter()
            .map(|(k, v)| {
                match v.as_str() {
                    "*" => k.clone(),                      // Valueless sugar: key
                    "?" => format!("{}=?", k),             // Explicit: key=?
                    "!" => format!("{}=!", k),             // Explicit: key=!
                    _ if Self::needs_quoting(v) => format!("{}={}", k, Self::quote_value(v)),
                    _ => format!("{}={}", k, v),
                }
            })
            .collect::<Vec<_>>()
            .join(";")
    }

    pub fn to_string(&self) -> String {
        let tags_str = self.tags_to_string();
        format!("{}:{}", self.prefix, tags_str)
    }

    /// Get the prefix of this tagged URN
    pub fn get_prefix(&self) -> &str {
        &self.prefix
    }

    /// Get a specific tag value
    /// Key is normalized to lowercase for lookup
    pub fn get_tag(&self, key: &str) -> Option<&String> {
        self.tags.get(&key.to_lowercase())
    }

    /// Check if this URN has a specific tag with a specific value
    /// Key is normalized to lowercase; value comparison is case-sensitive
    pub fn has_tag(&self, key: &str, value: &str) -> bool {
        self.tags
            .get(&key.to_lowercase())
            .map_or(false, |v| v == value)
    }

    /// Add or update a tag
    /// Key is normalized to lowercase; value is preserved as-is
    /// Returns error if value is empty (use "*" for wildcard)
    pub fn with_tag(mut self, key: String, value: String) -> Result<Self, TaggedUrnError> {
        if value.is_empty() {
            return Err(TaggedUrnError::EmptyTagComponent(format!(
                "empty value for key '{}' (use '*' for wildcard)",
                key
            )));
        }
        self.tags.insert(key.to_lowercase(), value);
        Ok(self)
    }

    /// Add or update a tag (infallible version for internal use where value is known valid)
    fn with_tag_unchecked(mut self, key: String, value: String) -> Self {
        self.tags.insert(key.to_lowercase(), value);
        self
    }

    /// Remove a tag
    /// Key is normalized to lowercase for case-insensitive removal
    pub fn without_tag(mut self, key: &str) -> Self {
        self.tags.remove(&key.to_lowercase());
        self
    }

    /// Check if this URN (instance) matches a pattern based on tag compatibility
    ///
    /// IMPORTANT: Both URNs must have the same prefix. Comparing URNs with
    /// different prefixes is a programming error and will return an error.
    ///
    /// Per-tag matching semantics:
    /// | Pattern Form | Interpretation              | Instance Missing | Instance = v | Instance = x≠v |
    /// |--------------|-----------------------------|--------------------|--------------|----------------|
    /// | (no entry)   | no constraint               | OK match           | OK match     | OK match       |
    /// | `K=?`        | no constraint (explicit)    | OK                 | OK           | OK             |
    /// | `K=!`        | **must-not-have**           | OK                 | NO           | NO             |
    /// | `K=*`        | **must-have, any value**    | NO                 | OK           | OK             |
    /// | `K=v`        | **must-have, exact value**  | NO                 | OK           | NO             |
    ///
    /// Special values work symmetrically on both instance and pattern sides.
    ///
    /// `self` is the instance, `pattern` is the pattern whose constraints must be satisfied.
    /// Equivalent to `pattern.accepts(self)`.
    pub fn conforms_to(&self, pattern: &TaggedUrn) -> Result<bool, TaggedUrnError> {
        Self::check_match(&self.tags, &self.prefix, &pattern.tags, &pattern.prefix)
    }

    /// Check if this URN (as a pattern) accepts the given instance.
    ///
    /// `self` is the pattern defining constraints, `instance` is tested against them.
    /// Equivalent to `instance.conforms_to(self)`.
    pub fn accepts(&self, instance: &TaggedUrn) -> Result<bool, TaggedUrnError> {
        Self::check_match(&instance.tags, &instance.prefix, &self.tags, &self.prefix)
    }

    /// Core matching: does `instance` satisfy `pattern`'s constraints?
    fn check_match(
        instance_tags: &BTreeMap<String, String>,
        instance_prefix: &str,
        pattern_tags: &BTreeMap<String, String>,
        pattern_prefix: &str,
    ) -> Result<bool, TaggedUrnError> {
        if instance_prefix != pattern_prefix {
            return Err(TaggedUrnError::PrefixMismatch {
                expected: pattern_prefix.to_string(),
                actual: instance_prefix.to_string(),
            });
        }

        let all_keys: std::collections::HashSet<&String> = instance_tags.keys()
            .chain(pattern_tags.keys())
            .collect();

        for key in all_keys {
            let inst = instance_tags.get(key).map(|s| s.as_str());
            let patt = pattern_tags.get(key).map(|s| s.as_str());

            if !Self::values_match(inst, patt) {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Check if instance value matches pattern constraint
    ///
    /// Full cross-product truth table:
    /// | Instance | Pattern | Match? | Reason |
    /// |----------|---------|--------|--------|
    /// | (none)   | (none)  | OK     | No constraint either side |
    /// | (none)   | K=?     | OK     | Pattern doesn't care |
    /// | (none)   | K=!     | OK     | Pattern wants absent, it is |
    /// | (none)   | K=*     | NO     | Pattern wants present |
    /// | (none)   | K=v     | NO     | Pattern wants exact value |
    /// | K=?      | (any)   | OK     | Instance doesn't care |
    /// | K=!      | (none)  | OK     | Symmetric: absent |
    /// | K=!      | K=?     | OK     | Pattern doesn't care |
    /// | K=!      | K=!     | OK     | Both want absent |
    /// | K=!      | K=*     | NO     | Conflict: absent vs present |
    /// | K=!      | K=v     | NO     | Conflict: absent vs value |
    /// | K=*      | (none)  | OK     | Pattern has no constraint |
    /// | K=*      | K=?     | OK     | Pattern doesn't care |
    /// | K=*      | K=!     | NO     | Conflict: present vs absent |
    /// | K=*      | K=*     | OK     | Both accept any presence |
    /// | K=*      | K=v     | OK     | Instance accepts any, v is fine |
    /// | K=v      | (none)  | OK     | Pattern has no constraint |
    /// | K=v      | K=?     | OK     | Pattern doesn't care |
    /// | K=v      | K=!     | NO     | Conflict: value vs absent |
    /// | K=v      | K=*     | OK     | Pattern wants any, v satisfies |
    /// | K=v      | K=v     | OK     | Exact match |
    /// | K=v      | K=w     | NO     | Value mismatch (v≠w) |
    fn values_match(inst: Option<&str>, patt: Option<&str>) -> bool {
        match (inst, patt) {
            // Pattern has no constraint (no entry or explicit ?)
            (_, None) | (_, Some("?")) => true,

            // Instance doesn't care (explicit ?)
            (Some("?"), _) => true,

            // Pattern: must-not-have (!)
            (None, Some("!")) => true,           // Instance absent, pattern wants absent
            (Some("!"), Some("!")) => true,      // Both say absent
            (Some(_), Some("!")) => false,       // Instance has value, pattern wants absent

            // Instance: must-not-have conflicts with pattern wanting value
            (Some("!"), Some("*")) => false,     // Conflict: absent vs present
            (Some("!"), Some(_)) => false,       // Conflict: absent vs value

            // Pattern: must-have-any (*)
            (None, Some("*")) => false,          // Instance missing, pattern wants present
            (Some(_), Some("*")) => true,        // Instance has value, pattern wants any

            // Pattern: exact value
            (None, Some(_)) => false,            // Instance missing, pattern wants value
            (Some("*"), Some(_)) => true,        // Instance accepts any, pattern's value is fine
            (Some(i), Some(p)) => i == p,        // Both have values, must match exactly
        }
    }

    pub fn conforms_to_str(&self, pattern_str: &str) -> Result<bool, TaggedUrnError> {
        let pattern = TaggedUrn::from_string(pattern_str)?;
        self.conforms_to(&pattern)
    }

    pub fn accepts_str(&self, instance_str: &str) -> Result<bool, TaggedUrnError> {
        let instance = TaggedUrn::from_string(instance_str)?;
        self.accepts(&instance)
    }

    /// Calculate specificity score for URN matching
    ///
    /// More specific URNs have higher scores and are preferred
    /// Graded scoring:
    /// - `K=v` (exact value): 3 points (most specific)
    /// - `K=*` (must-have-any): 2 points
    /// - `K=!` (must-not-have): 1 point
    /// - `K=?` (unspecified): 0 points (least specific)
    pub fn specificity(&self) -> usize {
        self.tags.values().map(|v| match v.as_str() {
            "?" => 0,
            "!" => 1,
            "*" => 2,
            _ => 3,  // exact value
        }).sum()
    }

    /// Get specificity as a tuple for tie-breaking
    ///
    /// Returns (exact_count, must_have_any_count, must_not_count)
    /// Compare tuples lexicographically when sum scores are equal
    pub fn specificity_tuple(&self) -> (usize, usize, usize) {
        let mut exact = 0;
        let mut must_have_any = 0;
        let mut must_not = 0;
        for v in self.tags.values() {
            match v.as_str() {
                "?" => {}
                "!" => must_not += 1,
                "*" => must_have_any += 1,
                _ => exact += 1,
            }
        }
        (exact, must_have_any, must_not)
    }

    /// Check if this URN is more specific than another
    pub fn is_more_specific_than(&self, other: &TaggedUrn) -> Result<bool, TaggedUrnError> {
        // First check prefix
        if self.prefix != other.prefix {
            return Err(TaggedUrnError::PrefixMismatch {
                expected: self.prefix.clone(),
                actual: other.prefix.clone(),
            });
        }

        // Then check if they're compatible
        if !self.is_compatible_with(other)? {
            return Ok(false);
        }

        Ok(self.specificity() > other.specificity())
    }

    /// Check if this URN is compatible with another
    ///
    /// Two URNs are compatible if they have the same prefix and can potentially match
    /// the same instances (i.e., there exists at least one instance that both patterns accept)
    ///
    /// Compatibility rules:
    /// - `K=v` and `K=w` (v≠w): NOT compatible (no instance can match both exact values)
    /// - `K=!` and `K=v`/`K=*`: NOT compatible (one requires absent, other requires present)
    /// - `K=v` and `K=*`: compatible (instance with K=v matches both)
    /// - `K=?` is compatible with anything (no constraint)
    /// - Missing entry is compatible with anything (no constraint)
    pub fn is_compatible_with(&self, other: &TaggedUrn) -> Result<bool, TaggedUrnError> {
        // First check prefix
        if self.prefix != other.prefix {
            return Err(TaggedUrnError::PrefixMismatch {
                expected: self.prefix.clone(),
                actual: other.prefix.clone(),
            });
        }

        // Get all unique tag keys from both URNs
        let mut all_keys = self
            .tags
            .keys()
            .cloned()
            .collect::<std::collections::HashSet<_>>();
        all_keys.extend(other.tags.keys().cloned());

        for key in all_keys {
            if !Self::values_compatible(
                self.tags.get(&key).map(|s| s.as_str()),
                other.tags.get(&key).map(|s| s.as_str()),
            ) {
                return Ok(false);
            }
        }

        Ok(true)
    }

    /// Check if two pattern values are compatible (could match the same instance)
    fn values_compatible(v1: Option<&str>, v2: Option<&str>) -> bool {
        match (v1, v2) {
            // Either missing or ? means no constraint - compatible with anything
            (None, _) | (_, None) => true,
            (Some("?"), _) | (_, Some("?")) => true,

            // Both are ! - compatible (both want absent)
            (Some("!"), Some("!")) => true,

            // One is ! and other is value or * - NOT compatible
            (Some("!"), Some(_)) | (Some(_), Some("!")) => false,

            // Both are * - compatible
            (Some("*"), Some("*")) => true,

            // One is * and other is value - compatible (value matches *)
            (Some("*"), Some(_)) | (Some(_), Some("*")) => true,

            // Both are specific values - must be equal
            (Some(a), Some(b)) => a == b,
        }
    }

    /// Create a wildcard version by replacing specific values with wildcards
    pub fn with_wildcard_tag(self, key: &str) -> Self {
        if self.tags.contains_key(key) {
            self.with_tag_unchecked(key.to_string(), "*".to_string())
        } else {
            self
        }
    }

    /// Create a subset URN with only specified tags
    pub fn subset(&self, keys: &[&str]) -> Self {
        let mut tags = BTreeMap::new();
        for &key in keys {
            if let Some(value) = self.tags.get(key) {
                tags.insert(key.to_string(), value.clone());
            }
        }
        Self {
            prefix: self.prefix.clone(),
            tags,
        }
    }

    /// Merge with another URN (other takes precedence for conflicts)
    /// Both must have the same prefix
    pub fn merge(&self, other: &TaggedUrn) -> Result<Self, TaggedUrnError> {
        if self.prefix != other.prefix {
            return Err(TaggedUrnError::PrefixMismatch {
                expected: self.prefix.clone(),
                actual: other.prefix.clone(),
            });
        }

        let mut tags = self.tags.clone();
        for (key, value) in &other.tags {
            tags.insert(key.clone(), value.clone());
        }
        Ok(Self {
            prefix: self.prefix.clone(),
            tags,
        })
    }

    pub fn canonical(tagged_urn: &str) -> Result<String, TaggedUrnError> {
        let tagged_urn_deserialized = TaggedUrn::from_string(tagged_urn)?;
        Ok(tagged_urn_deserialized.to_string())
    }

    pub fn canonical_option(tagged_urn: Option<&str>) -> Result<Option<String>, TaggedUrnError> {
        if let Some(cu) = tagged_urn {
            let tagged_urn_deserialized = TaggedUrn::from_string(cu)?;
            Ok(Some(tagged_urn_deserialized.to_string()))
        } else {
            Ok(None)
        }
    }
}

/// Errors that can occur when parsing or operating on tagged URNs
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum TaggedUrnError {
    /// Error code 1: Empty or malformed URN
    Empty,
    /// Error code 5: URN does not have a prefix (no colon found)
    MissingPrefix,
    /// Error code 10: Empty prefix (colon at start)
    EmptyPrefix,
    /// Error code 4: Tag not in key=value format
    InvalidTagFormat(String),
    /// Error code 2: Empty key or value component
    EmptyTagComponent(String),
    /// Error code 3: Disallowed character in key/value
    InvalidCharacter(String),
    /// Error code 6: Same key appears twice
    DuplicateKey(String),
    /// Error code 7: Key is purely numeric
    NumericKey(String),
    /// Error code 8: Quoted value never closed
    UnterminatedQuote(usize),
    /// Error code 9: Invalid escape in quoted value (only \" and \\ allowed)
    InvalidEscapeSequence(usize),
    /// Error code 11: Prefix mismatch when comparing URNs from different domains
    PrefixMismatch { expected: String, actual: String },
    /// Error code 12: Input has leading or trailing whitespace
    WhitespaceInInput(String),
}

impl fmt::Display for TaggedUrnError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TaggedUrnError::Empty => {
                write!(f, "Tagged URN cannot be empty")
            }
            TaggedUrnError::MissingPrefix => {
                write!(f, "Tagged URN must have a prefix followed by ':'")
            }
            TaggedUrnError::EmptyPrefix => {
                write!(f, "Tagged URN prefix cannot be empty")
            }
            TaggedUrnError::InvalidTagFormat(tag) => {
                write!(f, "Invalid tag format (must be key=value): {}", tag)
            }
            TaggedUrnError::EmptyTagComponent(tag) => {
                write!(f, "Tag key or value cannot be empty: {}", tag)
            }
            TaggedUrnError::InvalidCharacter(tag) => {
                write!(f, "Invalid character in tag: {}", tag)
            }
            TaggedUrnError::DuplicateKey(key) => {
                write!(f, "Duplicate tag key: {}", key)
            }
            TaggedUrnError::NumericKey(key) => {
                write!(f, "Tag key cannot be purely numeric: {}", key)
            }
            TaggedUrnError::UnterminatedQuote(pos) => {
                write!(f, "Unterminated quote at position {}", pos)
            }
            TaggedUrnError::InvalidEscapeSequence(pos) => {
                write!(
                    f,
                    "Invalid escape sequence at position {} (only \\\" and \\\\ allowed)",
                    pos
                )
            }
            TaggedUrnError::PrefixMismatch { expected, actual } => {
                write!(
                    f,
                    "Cannot compare URNs with different prefixes: '{}' vs '{}'",
                    expected, actual
                )
            }
            TaggedUrnError::WhitespaceInInput(input) => {
                write!(
                    f,
                    "Tagged URN has leading or trailing whitespace: '{}'",
                    input
                )
            }
        }
    }
}

impl std::error::Error for TaggedUrnError {}

impl FromStr for TaggedUrn {
    type Err = TaggedUrnError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        TaggedUrn::from_string(s)
    }
}

impl fmt::Display for TaggedUrn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

// Serde serialization support
impl Serialize for TaggedUrn {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.to_string())
    }
}

impl<'de> Deserialize<'de> for TaggedUrn {
    fn deserialize<D>(deserializer: D) -> Result<TaggedUrn, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        TaggedUrn::from_string(&s).map_err(serde::de::Error::custom)
    }
}

/// URN matching and selection utilities
pub struct UrnMatcher;

impl UrnMatcher {
    /// Find the most specific URN that conforms to a request's constraints.
    /// URNs are instances (capabilities), request is the pattern (requirement).
    /// All URNs must have the same prefix as the request.
    pub fn find_best_match<'a>(urns: &'a [TaggedUrn], request: &TaggedUrn) -> Result<Option<&'a TaggedUrn>, TaggedUrnError> {
        let mut best: Option<&TaggedUrn> = None;
        let mut best_specificity = 0;

        for urn in urns {
            if urn.conforms_to(request)? {
                let specificity = urn.specificity();
                if best.is_none() || specificity > best_specificity {
                    best = Some(urn);
                    best_specificity = specificity;
                }
            }
        }

        Ok(best)
    }

    /// Find all URNs that conform to a request's constraints, sorted by specificity.
    /// URNs are instances (capabilities), request is the pattern (requirement).
    /// All URNs must have the same prefix as the request.
    pub fn find_all_matches<'a>(urns: &'a [TaggedUrn], request: &TaggedUrn) -> Result<Vec<&'a TaggedUrn>, TaggedUrnError> {
        let mut results: Vec<&TaggedUrn> = Vec::new();

        for urn in urns {
            if urn.conforms_to(request)? {
                results.push(urn);
            }
        }

        // Sort by specificity (most specific first)
        results.sort_by_key(|urn| std::cmp::Reverse(urn.specificity()));
        Ok(results)
    }

    /// Check if two URN sets are compatible
    /// All URNs in both sets must have the same prefix
    pub fn are_compatible(urns1: &[TaggedUrn], urns2: &[TaggedUrn]) -> Result<bool, TaggedUrnError> {
        for u1 in urns1 {
            for u2 in urns2 {
                if u1.is_compatible_with(u2)? {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }
}

/// Builder for creating tagged URNs fluently
pub struct TaggedUrnBuilder {
    prefix: String,
    tags: BTreeMap<String, String>,
}

impl TaggedUrnBuilder {
    /// Create a new builder with a specified prefix (required)
    pub fn new(prefix: &str) -> Self {
        Self {
            prefix: prefix.to_lowercase(),
            tags: BTreeMap::new(),
        }
    }

    /// Add a tag with key (normalized to lowercase) and value (preserved as-is)
    /// Returns error if value is empty (use "*" for wildcard)
    pub fn tag(mut self, key: &str, value: &str) -> Result<Self, TaggedUrnError> {
        if value.is_empty() {
            return Err(TaggedUrnError::EmptyTagComponent(format!(
                "empty value for key '{}' (use '*' for wildcard)",
                key
            )));
        }
        self.tags.insert(key.to_lowercase(), value.to_string());
        Ok(self)
    }

	/// Add a tag with key (normalized to lowercase) and wildcard value
    pub fn solo_tag(mut self, key: &str) -> Self {
        self.tags.insert(key.to_lowercase(), "*".to_string());
        self
    }

    pub fn build(self) -> Result<TaggedUrn, TaggedUrnError> {
        if self.tags.is_empty() {
            return Err(TaggedUrnError::Empty);
        }
        Ok(TaggedUrn {
            prefix: self.prefix,
            tags: self.tags,
        })
    }

    /// Build allowing empty tags (creates an empty URN that matches everything)
    pub fn build_allow_empty(self) -> TaggedUrn {
        TaggedUrn {
            prefix: self.prefix,
            tags: self.tags,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tagged_urn_creation() {
        let urn = TaggedUrn::from_string("cap:op=generate;ext=pdf;target=thumbnail;").unwrap();
        assert_eq!(urn.get_prefix(), "cap");
        assert_eq!(urn.get_tag("op"), Some(&"generate".to_string()));
        assert_eq!(urn.get_tag("target"), Some(&"thumbnail".to_string()));
        assert_eq!(urn.get_tag("ext"), Some(&"pdf".to_string()));
    }

    #[test]
    fn test_custom_prefix() {
        let urn = TaggedUrn::from_string("myapp:op=generate;ext=pdf").unwrap();
        assert_eq!(urn.get_prefix(), "myapp");
        assert_eq!(urn.get_tag("op"), Some(&"generate".to_string()));
        assert_eq!(urn.to_string(), "myapp:ext=pdf;op=generate");
    }

    #[test]
    fn test_prefix_case_insensitive() {
        let urn1 = TaggedUrn::from_string("CAP:op=test").unwrap();
        let urn2 = TaggedUrn::from_string("cap:op=test").unwrap();
        let urn3 = TaggedUrn::from_string("Cap:op=test").unwrap();

        assert_eq!(urn1.get_prefix(), "cap");
        assert_eq!(urn2.get_prefix(), "cap");
        assert_eq!(urn3.get_prefix(), "cap");
        assert_eq!(urn1, urn2);
        assert_eq!(urn2, urn3);
    }

    #[test]
    fn test_prefix_mismatch_error() {
        let urn1 = TaggedUrn::from_string("cap:op=test").unwrap();
        let urn2 = TaggedUrn::from_string("myapp:op=test").unwrap();

        // urn1 (cap) is instance, urn2 (myapp) is pattern
        // expected = pattern prefix, actual = instance prefix
        let result = urn1.conforms_to(&urn2);
        assert!(result.is_err());
        if let Err(TaggedUrnError::PrefixMismatch { expected, actual }) = result {
            assert_eq!(expected, "myapp");
            assert_eq!(actual, "cap");
        } else {
            panic!("Expected PrefixMismatch error");
        }
    }

    #[test]
    fn test_builder_with_prefix() {
        let urn = TaggedUrnBuilder::new("custom")
            .tag("key", "value").unwrap()
            .build()
            .unwrap();

        assert_eq!(urn.get_prefix(), "custom");
        assert_eq!(urn.to_string(), "custom:key=value");
    }

    #[test]
    fn test_unquoted_values_lowercased() {
        // Unquoted values are normalized to lowercase
        let urn = TaggedUrn::from_string("cap:OP=Generate;EXT=PDF;Target=Thumbnail;").unwrap();

        // Keys are always lowercase
        assert_eq!(urn.get_tag("op"), Some(&"generate".to_string()));
        assert_eq!(urn.get_tag("ext"), Some(&"pdf".to_string()));
        assert_eq!(urn.get_tag("target"), Some(&"thumbnail".to_string()));

        // Key lookup is case-insensitive
        assert_eq!(urn.get_tag("OP"), Some(&"generate".to_string()));
        assert_eq!(urn.get_tag("Op"), Some(&"generate".to_string()));

        // Both URNs parse to same lowercase values (same tags, same values)
        let urn2 = TaggedUrn::from_string("cap:op=generate;ext=pdf;target=thumbnail;").unwrap();
        assert_eq!(urn.to_string(), urn2.to_string());
        assert_eq!(urn, urn2);
    }

    #[test]
    fn test_quoted_values_preserve_case() {
        // Quoted values preserve their case
        let urn = TaggedUrn::from_string(r#"cap:key="Value With Spaces""#).unwrap();
        assert_eq!(urn.get_tag("key"), Some(&"Value With Spaces".to_string()));

        // Key is still lowercase
        let urn2 = TaggedUrn::from_string(r#"cap:KEY="Value With Spaces""#).unwrap();
        assert_eq!(urn2.get_tag("key"), Some(&"Value With Spaces".to_string()));

        // Unquoted vs quoted case difference
        let unquoted = TaggedUrn::from_string("cap:key=UPPERCASE").unwrap();
        let quoted = TaggedUrn::from_string(r#"cap:key="UPPERCASE""#).unwrap();
        assert_eq!(unquoted.get_tag("key"), Some(&"uppercase".to_string())); // lowercase
        assert_eq!(quoted.get_tag("key"), Some(&"UPPERCASE".to_string())); // preserved
        assert_ne!(unquoted, quoted); // NOT equal
    }

    #[test]
    fn test_quoted_value_special_chars() {
        // Semicolons in quoted values
        let urn = TaggedUrn::from_string(r#"cap:key="value;with;semicolons""#).unwrap();
        assert_eq!(urn.get_tag("key"), Some(&"value;with;semicolons".to_string()));

        // Equals in quoted values
        let urn2 = TaggedUrn::from_string(r#"cap:key="value=with=equals""#).unwrap();
        assert_eq!(urn2.get_tag("key"), Some(&"value=with=equals".to_string()));

        // Spaces in quoted values
        let urn3 = TaggedUrn::from_string(r#"cap:key="hello world""#).unwrap();
        assert_eq!(urn3.get_tag("key"), Some(&"hello world".to_string()));
    }

    #[test]
    fn test_quoted_value_escape_sequences() {
        // Escaped quotes
        let urn = TaggedUrn::from_string(r#"cap:key="value\"quoted\"""#).unwrap();
        assert_eq!(urn.get_tag("key"), Some(&r#"value"quoted""#.to_string()));

        // Escaped backslashes
        let urn2 = TaggedUrn::from_string(r#"cap:key="path\\file""#).unwrap();
        assert_eq!(urn2.get_tag("key"), Some(&r#"path\file"#.to_string()));

        // Mixed escapes
        let urn3 = TaggedUrn::from_string(r#"cap:key="say \"hello\\world\"""#).unwrap();
        assert_eq!(urn3.get_tag("key"), Some(&r#"say "hello\world""#.to_string()));
    }

    #[test]
    fn test_mixed_quoted_unquoted() {
        let urn = TaggedUrn::from_string(r#"cap:a="Quoted";b=simple"#).unwrap();
        assert_eq!(urn.get_tag("a"), Some(&"Quoted".to_string()));
        assert_eq!(urn.get_tag("b"), Some(&"simple".to_string()));
    }

    #[test]
    fn test_unterminated_quote_error() {
        let result = TaggedUrn::from_string(r#"cap:key="unterminated"#);
        assert!(result.is_err());
        if let Err(e) = result {
            assert!(matches!(e, TaggedUrnError::UnterminatedQuote(_)));
        }
    }

    #[test]
    fn test_invalid_escape_sequence_error() {
        let result = TaggedUrn::from_string(r#"cap:key="bad\n""#);
        assert!(result.is_err());
        if let Err(e) = result {
            assert!(matches!(e, TaggedUrnError::InvalidEscapeSequence(_)));
        }

        // Invalid escape at end
        let result2 = TaggedUrn::from_string(r#"cap:key="bad\x""#);
        assert!(result2.is_err());
        if let Err(e) = result2 {
            assert!(matches!(e, TaggedUrnError::InvalidEscapeSequence(_)));
        }
    }

    #[test]
    fn test_serialization_smart_quoting() {
        // Simple lowercase value - no quoting needed
        let urn = TaggedUrnBuilder::new("cap").tag("key", "simple").unwrap().build().unwrap();
        assert_eq!(urn.to_string(), "cap:key=simple");

        // Value with spaces - needs quoting
        let urn2 = TaggedUrnBuilder::new("cap")
            .tag("key", "has spaces").unwrap()
            .build()
            .unwrap();
        assert_eq!(urn2.to_string(), r#"cap:key="has spaces""#);

        // Value with semicolons - needs quoting
        let urn3 = TaggedUrnBuilder::new("cap")
            .tag("key", "has;semi").unwrap()
            .build()
            .unwrap();
        assert_eq!(urn3.to_string(), r#"cap:key="has;semi""#);

        // Value with uppercase - needs quoting to preserve
        let urn4 = TaggedUrnBuilder::new("cap")
            .tag("key", "HasUpper").unwrap()
            .build()
            .unwrap();
        assert_eq!(urn4.to_string(), r#"cap:key="HasUpper""#);

        // Value with quotes - needs quoting and escaping
        let urn5 = TaggedUrnBuilder::new("cap")
            .tag("key", r#"has"quote"#).unwrap()
            .build()
            .unwrap();
        assert_eq!(urn5.to_string(), r#"cap:key="has\"quote""#);

        // Value with backslashes - needs quoting and escaping
        let urn6 = TaggedUrnBuilder::new("cap")
            .tag("key", r#"path\file"#).unwrap()
            .build()
            .unwrap();
        assert_eq!(urn6.to_string(), r#"cap:key="path\\file""#);
    }

    #[test]
    fn test_round_trip_simple() {
        let original = "cap:op=generate;ext=pdf";
        let urn = TaggedUrn::from_string(original).unwrap();
        let serialized = urn.to_string();
        let reparsed = TaggedUrn::from_string(&serialized).unwrap();
        assert_eq!(urn, reparsed);
    }

    #[test]
    fn test_round_trip_quoted() {
        let original = r#"cap:key="Value With Spaces""#;
        let urn = TaggedUrn::from_string(original).unwrap();
        let serialized = urn.to_string();
        let reparsed = TaggedUrn::from_string(&serialized).unwrap();
        assert_eq!(urn, reparsed);
        assert_eq!(reparsed.get_tag("key"), Some(&"Value With Spaces".to_string()));
    }

    #[test]
    fn test_round_trip_escapes() {
        let original = r#"cap:key="value\"with\\escapes""#;
        let urn = TaggedUrn::from_string(original).unwrap();
        assert_eq!(urn.get_tag("key"), Some(&r#"value"with\escapes"#.to_string()));
        let serialized = urn.to_string();
        let reparsed = TaggedUrn::from_string(&serialized).unwrap();
        assert_eq!(urn, reparsed);
    }

    #[test]
    fn test_prefix_required() {
        // Missing prefix should fail
        assert!(TaggedUrn::from_string("op=generate;ext=pdf").is_err());

        // Valid prefix should work
        let urn = TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap();
        assert_eq!(urn.get_tag("op"), Some(&"generate".to_string()));

        // Case-insensitive prefix
        let urn2 = TaggedUrn::from_string("CAP:op=generate").unwrap();
        assert_eq!(urn2.get_tag("op"), Some(&"generate".to_string()));
    }

    #[test]
    fn test_trailing_semicolon_equivalence() {
        // Both with and without trailing semicolon should be equivalent
        let urn1 = TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap();
        let urn2 = TaggedUrn::from_string("cap:op=generate;ext=pdf;").unwrap();

        // They should be equal
        assert_eq!(urn1, urn2);

        // They should have same hash
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut hasher1 = DefaultHasher::new();
        urn1.hash(&mut hasher1);
        let hash1 = hasher1.finish();

        let mut hasher2 = DefaultHasher::new();
        urn2.hash(&mut hasher2);
        let hash2 = hasher2.finish();

        assert_eq!(hash1, hash2);

        // They should have same string representation (canonical form)
        assert_eq!(urn1.to_string(), urn2.to_string());

        // They should match each other
        assert!(urn1.conforms_to(&urn2).unwrap());
        assert!(urn2.conforms_to(&urn1).unwrap());
    }

    #[test]
    fn test_canonical_string_format() {
        let urn = TaggedUrn::from_string("cap:op=generate;target=thumbnail;ext=pdf").unwrap();
        // Should be sorted alphabetically and have no trailing semicolon in canonical form
        // Alphabetical order: ext < op < target
        assert_eq!(
            urn.to_string(),
            "cap:ext=pdf;op=generate;target=thumbnail"
        );
    }

    #[test]
    fn test_tag_matching() {
        let urn = TaggedUrn::from_string("cap:op=generate;ext=pdf;target=thumbnail;").unwrap();

        // Exact match
        let request1 =
            TaggedUrn::from_string("cap:op=generate;ext=pdf;target=thumbnail;").unwrap();
        assert!(urn.conforms_to(&request1).unwrap());

        // Subset match
        let request2 = TaggedUrn::from_string("cap:op=generate").unwrap();
        assert!(urn.conforms_to(&request2).unwrap());

        // Wildcard request should match specific URN
        let request3 = TaggedUrn::from_string("cap:ext=*").unwrap();
        assert!(urn.conforms_to(&request3).unwrap()); // URN has ext=pdf, request accepts any ext

        // No match - conflicting value
        let request4 = TaggedUrn::from_string("cap:op=extract").unwrap();
        assert!(!urn.conforms_to(&request4).unwrap());
    }

    #[test]
    fn test_matching_case_sensitive_values() {
        // Values with different case should NOT match
        let urn1 = TaggedUrn::from_string(r#"cap:key="Value""#).unwrap();
        let urn2 = TaggedUrn::from_string(r#"cap:key="value""#).unwrap();
        assert!(!urn1.conforms_to(&urn2).unwrap());
        assert!(!urn2.conforms_to(&urn1).unwrap());

        // Same case should match
        let urn3 = TaggedUrn::from_string(r#"cap:key="Value""#).unwrap();
        assert!(urn1.conforms_to(&urn3).unwrap());
    }

    #[test]
    fn test_missing_tag_handling() {
        // NEW SEMANTICS: Missing tag in instance means the tag doesn't exist.
        // Pattern constraints must be satisfied by instance.

        let urn = TaggedUrn::from_string("cap:op=generate").unwrap();

        // Pattern with tag that instance doesn't have: NO MATCH
        // Pattern ext=pdf requires instance to have ext=pdf, but instance doesn't have ext
        let pattern1 = TaggedUrn::from_string("cap:ext=pdf").unwrap();
        assert!(!urn.conforms_to(&pattern1).unwrap()); // Instance missing ext, pattern wants ext=pdf

        // Pattern missing tag = no constraint: MATCH
        // Instance has op=generate, pattern has no constraint on op
        let urn2 = TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap();
        let pattern2 = TaggedUrn::from_string("cap:op=generate").unwrap();
        assert!(urn2.conforms_to(&pattern2).unwrap()); // Instance has ext=pdf, pattern doesn't constrain ext

        // To match any value of a tag, use explicit ? or *
        let pattern3 = TaggedUrn::from_string("cap:ext=?").unwrap(); // ? = no constraint
        assert!(urn.conforms_to(&pattern3).unwrap()); // Instance missing ext, pattern doesn't care

        // * means must-have-any - instance must have the tag
        let pattern4 = TaggedUrn::from_string("cap:ext=*").unwrap();
        assert!(!urn.conforms_to(&pattern4).unwrap()); // Instance missing ext, pattern requires ext to be present
    }

    #[test]
    fn test_specificity() {
        // NEW GRADED SPECIFICITY:
        // K=v (exact value): 3 points
        // K=* (must-have-any): 2 points
        // K=! (must-not-have): 1 point
        // K=? (unspecified): 0 points

        let urn1 = TaggedUrn::from_string("cap:general").unwrap(); // value-less = * = 2 points
        let urn2 = TaggedUrn::from_string("cap:op=generate").unwrap(); // exact = 3 points
        let urn3 = TaggedUrn::from_string("cap:op=*;ext=pdf").unwrap(); // * + exact = 2 + 3 = 5 points
        let urn4 = TaggedUrn::from_string("cap:op=?").unwrap(); // ? = 0 points
        let urn5 = TaggedUrn::from_string("cap:op=!").unwrap(); // ! = 1 point

        assert_eq!(urn1.specificity(), 2); // * = 2
        assert_eq!(urn2.specificity(), 3); // exact = 3
        assert_eq!(urn3.specificity(), 5); // * + exact = 2 + 3
        assert_eq!(urn4.specificity(), 0); // ? = 0
        assert_eq!(urn5.specificity(), 1); // ! = 1

        // Specificity tuple for tie-breaking: (exact_count, must_have_any_count, must_not_count)
        assert_eq!(urn2.specificity_tuple(), (1, 0, 0));
        assert_eq!(urn3.specificity_tuple(), (1, 1, 0));
        assert_eq!(urn5.specificity_tuple(), (0, 0, 1));

        assert!(urn2.is_more_specific_than(&urn1).unwrap()); // 3 > 2
    }

    #[test]
    fn test_builder() {
        let urn = TaggedUrnBuilder::new("cap")
            .tag("op", "generate").unwrap()
            .tag("target", "thumbnail").unwrap()
            .tag("ext", "pdf").unwrap()
            .tag("output", "binary").unwrap()
            .build()
            .unwrap();

        assert_eq!(urn.get_tag("op"), Some(&"generate".to_string()));
        assert_eq!(urn.get_tag("output"), Some(&"binary".to_string()));
    }

    #[test]
    fn test_builder_preserves_case() {
        let urn = TaggedUrnBuilder::new("cap")
            .tag("KEY", "ValueWithCase").unwrap()
            .build()
            .unwrap();

        // Key is lowercase
        assert_eq!(urn.get_tag("key"), Some(&"ValueWithCase".to_string()));
        // Value case preserved, so needs quoting
        assert_eq!(urn.to_string(), r#"cap:key="ValueWithCase""#);
    }

    #[test]
    fn test_compatibility() {
        let urn1 = TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap();
        let urn2 = TaggedUrn::from_string("cap:op=generate;format=*").unwrap();
        let urn3 = TaggedUrn::from_string("cap:image;op=extract").unwrap();

        assert!(urn1.is_compatible_with(&urn2).unwrap());
        assert!(urn2.is_compatible_with(&urn1).unwrap());
        assert!(!urn1.is_compatible_with(&urn3).unwrap());

        // Missing tags are treated as wildcards for compatibility
        let urn4 = TaggedUrn::from_string("cap:op=generate").unwrap();
        assert!(urn1.is_compatible_with(&urn4).unwrap());
        assert!(urn4.is_compatible_with(&urn1).unwrap());
    }

    #[test]
    fn test_best_match() {
        let urns = vec![
            TaggedUrn::from_string("cap:op=*").unwrap(),
            TaggedUrn::from_string("cap:op=generate").unwrap(),
            TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap(),
        ];

        let request = TaggedUrn::from_string("cap:op=generate").unwrap();
        let best = UrnMatcher::find_best_match(&urns, &request).unwrap().unwrap();

        // Most specific URN that can handle the request
        // Alphabetical order: ext < op
        assert_eq!(best.to_string(), "cap:ext=pdf;op=generate");
    }

    #[test]
    fn test_merge_and_subset() {
        let urn1 = TaggedUrn::from_string("cap:op=generate").unwrap();
        let urn2 = TaggedUrn::from_string("cap:ext=pdf;output=binary").unwrap();

        let merged = urn1.merge(&urn2).unwrap();
        // Alphabetical order: ext < op < output
        assert_eq!(
            merged.to_string(),
            "cap:ext=pdf;op=generate;output=binary"
        );

        let subset = merged.subset(&["type", "ext"]);
        assert_eq!(subset.to_string(), "cap:ext=pdf");
    }

    #[test]
    fn test_merge_prefix_mismatch() {
        let urn1 = TaggedUrn::from_string("cap:op=generate").unwrap();
        let urn2 = TaggedUrn::from_string("myapp:ext=pdf").unwrap();

        let result = urn1.merge(&urn2);
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), TaggedUrnError::PrefixMismatch { .. }));
    }

    #[test]
    fn test_wildcard_tag() {
        let urn = TaggedUrn::from_string("cap:ext=pdf").unwrap();
        let wildcarded = urn.clone().with_wildcard_tag("ext");

        // Wildcard serializes as value-less tag
        assert_eq!(wildcarded.to_string(), "cap:ext");

        // Test that wildcarded URN can match more requests
        let request = TaggedUrn::from_string("cap:ext=jpg").unwrap();
        assert!(!urn.conforms_to(&request).unwrap());
        assert!(wildcarded.conforms_to(&TaggedUrn::from_string("cap:ext").unwrap()).unwrap());
    }

    #[test]
    fn test_empty_tagged_urn() {
        // Empty tagged URN is valid
        let empty_urn = TaggedUrn::from_string("cap:").unwrap();
        assert_eq!(empty_urn.tags.len(), 0);
        assert_eq!(empty_urn.to_string(), "cap:");

        // NEW SEMANTICS:
        // Empty PATTERN matches any INSTANCE (pattern has no constraints)
        // Empty INSTANCE only matches patterns that have no required tags

        let specific_urn = TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap();

        // Empty instance vs specific pattern: NO MATCH
        // Pattern requires op=generate and ext=pdf, instance doesn't have them
        assert!(!empty_urn.conforms_to(&specific_urn).unwrap());

        // Specific instance vs empty pattern: MATCH
        // Pattern has no constraints, instance can have anything
        assert!(specific_urn.conforms_to(&empty_urn).unwrap());

        // Empty instance vs empty pattern: MATCH
        assert!(empty_urn.conforms_to(&empty_urn).unwrap());

        // With trailing semicolon
        let empty_urn2 = TaggedUrn::from_string("cap:;").unwrap();
        assert_eq!(empty_urn2.tags.len(), 0);
    }

    #[test]
    fn test_empty_with_custom_prefix() {
        let empty_urn = TaggedUrn::from_string("myapp:").unwrap();
        assert_eq!(empty_urn.get_prefix(), "myapp");
        assert_eq!(empty_urn.tags.len(), 0);
        assert_eq!(empty_urn.to_string(), "myapp:");
    }

    #[test]
    fn test_extended_character_support() {
        // Test forward slashes and colons in tag components
        let urn = TaggedUrn::from_string("cap:url=https://example_org/api;path=/some/file").unwrap();
        assert_eq!(
            urn.get_tag("url"),
            Some(&"https://example_org/api".to_string())
        );
        assert_eq!(urn.get_tag("path"), Some(&"/some/file".to_string()));
    }

    #[test]
    fn test_wildcard_restrictions() {
        // Wildcard should be rejected in keys
        assert!(TaggedUrn::from_string("cap:*=value").is_err());

        // Wildcard should be accepted in values
        let urn = TaggedUrn::from_string("cap:key=*").unwrap();
        assert_eq!(urn.get_tag("key"), Some(&"*".to_string()));
    }

    #[test]
    fn test_duplicate_key_rejection() {
        let result = TaggedUrn::from_string("cap:key=value1;key=value2");
        assert!(result.is_err());
        if let Err(e) = result {
            assert!(matches!(e, TaggedUrnError::DuplicateKey(_)));
        }
    }

    #[test]
    fn test_numeric_key_restriction() {
        // Pure numeric keys should be rejected
        assert!(TaggedUrn::from_string("cap:123=value").is_err());

        // Mixed alphanumeric keys should be allowed
        assert!(TaggedUrn::from_string("cap:key123=value").is_ok());
        assert!(TaggedUrn::from_string("cap:123key=value").is_ok());

        // Pure numeric values should be allowed
        assert!(TaggedUrn::from_string("cap:key=123").is_ok());
    }

    #[test]
    fn test_empty_value_error() {
        assert!(TaggedUrn::from_string("cap:key=").is_err());
        assert!(TaggedUrn::from_string("cap:key=;other=value").is_err());
    }

    #[test]
    fn test_has_tag_case_sensitive() {
        let urn = TaggedUrn::from_string(r#"cap:key="Value""#).unwrap();

        // Exact case match works
        assert!(urn.has_tag("key", "Value"));

        // Different case does not match
        assert!(!urn.has_tag("key", "value"));
        assert!(!urn.has_tag("key", "VALUE"));

        // Key lookup is case-insensitive
        assert!(urn.has_tag("KEY", "Value"));
        assert!(urn.has_tag("Key", "Value"));
    }

    #[test]
    fn test_with_tag_preserves_value() {
        let urn = TaggedUrn::empty("cap".to_string()).with_tag("key".to_string(), "ValueWithCase".to_string()).unwrap();
        assert_eq!(urn.get_tag("key"), Some(&"ValueWithCase".to_string()));
    }

    #[test]
    fn test_with_tag_rejects_empty_value() {
        let result = TaggedUrn::empty("cap".to_string()).with_tag("key".to_string(), "".to_string());
        assert!(result.is_err());
        if let Err(TaggedUrnError::EmptyTagComponent(msg)) = result {
            assert!(msg.contains("empty value"));
        } else {
            panic!("Expected EmptyTagComponent error");
        }
    }

    #[test]
    fn test_builder_rejects_empty_value() {
        let result = TaggedUrnBuilder::new("cap").tag("key", "");
        assert!(result.is_err());
        if let Err(TaggedUrnError::EmptyTagComponent(msg)) = result {
            assert!(msg.contains("empty value"));
        } else {
            panic!("Expected EmptyTagComponent error");
        }
    }

    #[test]
    fn test_semantic_equivalence() {
        // Unquoted and quoted simple lowercase values are equivalent
        let unquoted = TaggedUrn::from_string("cap:key=simple").unwrap();
        let quoted = TaggedUrn::from_string(r#"cap:key="simple""#).unwrap();
        assert_eq!(unquoted, quoted);

        // Both serialize the same way (unquoted)
        assert_eq!(unquoted.to_string(), "cap:key=simple");
        assert_eq!(quoted.to_string(), "cap:key=simple");
    }

    // ============================================================================
    // MATCHING SEMANTICS SPECIFICATION TESTS
    // These 9 tests verify the exact matching semantics from RULES.md Sections 12-17
    // All implementations (Rust, Go, JS, ObjC) must pass these identically
    // ============================================================================

    #[test]
    fn test_matching_semantics_test1_exact_match() {
        // Test 1: Exact match
        // URN:     cap:op=generate;ext=pdf
        // Request: cap:op=generate;ext=pdf
        // Result:  MATCH
        let urn = TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap();
        let request = TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap();
        assert!(urn.conforms_to(&request).unwrap(), "Test 1: Exact match should succeed");
    }

    #[test]
    fn test_matching_semantics_test2_instance_missing_tag() {
        // Test 2: Instance missing tag
        // Instance: cap:op=generate
        // Pattern:  cap:op=generate;ext=pdf
        // Result:   NO MATCH (pattern requires ext=pdf, instance doesn't have ext)
        //
        // NEW SEMANTICS: Missing tag in instance means it doesn't exist.
        // Pattern K=v requires instance to have K=v.
        let instance = TaggedUrn::from_string("cap:op=generate").unwrap();
        let pattern = TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap();
        assert!(!instance.conforms_to(&pattern).unwrap(), "Test 2: Instance missing tag should NOT match when pattern requires it");

        // To accept any ext (or missing), use pattern with ext=?
        let pattern_optional = TaggedUrn::from_string("cap:op=generate;ext=?").unwrap();
        assert!(instance.conforms_to(&pattern_optional).unwrap(), "Pattern with ext=? should match instance without ext");
    }

    #[test]
    fn test_matching_semantics_test3_urn_has_extra_tag() {
        // Test 3: URN has extra tag
        // URN:     cap:op=generate;ext=pdf;version=2
        // Request: cap:op=generate;ext=pdf
        // Result:  MATCH (request doesn't constrain version)
        let urn = TaggedUrn::from_string("cap:op=generate;ext=pdf;version=2").unwrap();
        let request = TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap();
        assert!(urn.conforms_to(&request).unwrap(), "Test 3: URN with extra tag should match");
    }

    #[test]
    fn test_matching_semantics_test4_request_has_wildcard() {
        // Test 4: Request has wildcard
        // URN:     cap:op=generate;ext=pdf
        // Request: cap:op=generate;ext=*
        // Result:  MATCH (request accepts any ext)
        let urn = TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap();
        let request = TaggedUrn::from_string("cap:op=generate;ext=*").unwrap();
        assert!(urn.conforms_to(&request).unwrap(), "Test 4: Request wildcard should match");
    }

    #[test]
    fn test_matching_semantics_test5_urn_has_wildcard() {
        // Test 5: URN has wildcard
        // URN:     cap:op=generate;ext=*
        // Request: cap:op=generate;ext=pdf
        // Result:  MATCH (URN handles any ext)
        let urn = TaggedUrn::from_string("cap:op=generate;ext=*").unwrap();
        let request = TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap();
        assert!(urn.conforms_to(&request).unwrap(), "Test 5: URN wildcard should match");
    }

    #[test]
    fn test_matching_semantics_test6_value_mismatch() {
        // Test 6: Value mismatch
        // URN:     cap:op=generate;ext=pdf
        // Request: cap:op=generate;ext=docx
        // Result:  NO MATCH
        let urn = TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap();
        let request = TaggedUrn::from_string("cap:op=generate;ext=docx").unwrap();
        assert!(!urn.conforms_to(&request).unwrap(), "Test 6: Value mismatch should not match");
    }

    #[test]
    fn test_matching_semantics_test7_pattern_has_extra_tag() {
        // Test 7: Pattern has extra tag that instance doesn't have
        // Instance: cap:op=generate_thumbnail;out="media:binary"
        // Pattern:  cap:op=generate_thumbnail;out="media:binary";ext=wav
        // Result:   NO MATCH (pattern requires ext=wav, instance doesn't have ext)
        //
        // NEW SEMANTICS: Pattern K=v requires instance to have K=v
        let instance = TaggedUrn::from_string(r#"cap:op=generate_thumbnail;out="media:binary""#).unwrap();
        let pattern = TaggedUrn::from_string(r#"cap:op=generate_thumbnail;out="media:binary";ext=wav"#).unwrap();
        assert!(!instance.conforms_to(&pattern).unwrap(), "Test 7: Instance missing ext should NOT match when pattern requires ext=wav");

        // Instance vs pattern that doesn't constrain ext: MATCH
        let pattern_no_ext = TaggedUrn::from_string(r#"cap:op=generate_thumbnail;out="media:binary""#).unwrap();
        assert!(instance.conforms_to(&pattern_no_ext).unwrap());
    }

    #[test]
    fn test_matching_semantics_test8_empty_pattern_matches_anything() {
        // Test 8: Empty PATTERN matches any INSTANCE
        // Instance: cap:op=generate;ext=pdf
        // Pattern:  cap:
        // Result:   MATCH (pattern has no constraints)
        //
        // NEW SEMANTICS: Empty pattern = no constraints = matches any instance
        // But empty instance only matches patterns that don't require tags
        let instance = TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap();
        let empty_pattern = TaggedUrn::from_string("cap:").unwrap();
        assert!(instance.conforms_to(&empty_pattern).unwrap(), "Test 8: Any instance should match empty pattern");

        // Empty instance vs pattern with requirements: NO MATCH
        let empty_instance = TaggedUrn::from_string("cap:").unwrap();
        let pattern = TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap();
        assert!(!empty_instance.conforms_to(&pattern).unwrap(), "Empty instance should NOT match pattern with requirements");
    }

    #[test]
    fn test_matching_semantics_test9_cross_dimension_constraints() {
        // Test 9: Cross-dimension constraints
        // Instance: cap:op=generate
        // Pattern:  cap:ext=pdf
        // Result:   NO MATCH (pattern requires ext=pdf, instance doesn't have ext)
        //
        // NEW SEMANTICS: Pattern K=v requires instance to have K=v
        let instance = TaggedUrn::from_string("cap:op=generate").unwrap();
        let pattern = TaggedUrn::from_string("cap:ext=pdf").unwrap();
        assert!(!instance.conforms_to(&pattern).unwrap(), "Test 9: Instance without ext should NOT match pattern requiring ext");

        // Instance with ext vs pattern with different tag only: MATCH
        let instance2 = TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap();
        let pattern2 = TaggedUrn::from_string("cap:ext=pdf").unwrap();
        assert!(instance2.conforms_to(&pattern2).unwrap(), "Instance with ext=pdf should match pattern requiring ext=pdf");
    }

    #[test]
    fn test_matching_different_prefixes_error() {
        // URNs with different prefixes should cause an error, not just return false
        let urn1 = TaggedUrn::from_string("cap:op=test").unwrap();
        let urn2 = TaggedUrn::from_string("other:op=test").unwrap();

        let result = urn1.conforms_to(&urn2);
        assert!(result.is_err());

        let result2 = urn1.is_compatible_with(&urn2);
        assert!(result2.is_err());

        let result3 = urn1.is_more_specific_than(&urn2);
        assert!(result3.is_err());
    }

    // ============================================================================
    // VALUE-LESS TAG TESTS
    // Value-less tags are equivalent to wildcard tags (key=*)
    // ============================================================================

    #[test]
    fn test_valueless_tag_parsing_single() {
        // Single value-less tag
        let urn = TaggedUrn::from_string("cap:optimize").unwrap();
        assert_eq!(urn.get_tag("optimize"), Some(&"*".to_string()));
        // Serializes as value-less (no =*)
        assert_eq!(urn.to_string(), "cap:optimize");
    }

    #[test]
    fn test_valueless_tag_parsing_multiple() {
        // Multiple value-less tags
        let urn = TaggedUrn::from_string("cap:fast;optimize;secure").unwrap();
        assert_eq!(urn.get_tag("fast"), Some(&"*".to_string()));
        assert_eq!(urn.get_tag("optimize"), Some(&"*".to_string()));
        assert_eq!(urn.get_tag("secure"), Some(&"*".to_string()));
        // Serializes alphabetically as value-less
        assert_eq!(urn.to_string(), "cap:fast;optimize;secure");
    }

    #[test]
    fn test_valueless_tag_mixed_with_valued() {
        // Mix of value-less and valued tags
        let urn = TaggedUrn::from_string("cap:op=generate;optimize;ext=pdf;secure").unwrap();
        assert_eq!(urn.get_tag("op"), Some(&"generate".to_string()));
        assert_eq!(urn.get_tag("optimize"), Some(&"*".to_string()));
        assert_eq!(urn.get_tag("ext"), Some(&"pdf".to_string()));
        assert_eq!(urn.get_tag("secure"), Some(&"*".to_string()));
        // Serializes alphabetically
        assert_eq!(urn.to_string(), "cap:ext=pdf;op=generate;optimize;secure");
    }

    #[test]
    fn test_valueless_tag_at_end() {
        // Value-less tag at the end (no trailing semicolon)
        let urn = TaggedUrn::from_string("cap:op=generate;optimize").unwrap();
        assert_eq!(urn.get_tag("op"), Some(&"generate".to_string()));
        assert_eq!(urn.get_tag("optimize"), Some(&"*".to_string()));
        assert_eq!(urn.to_string(), "cap:op=generate;optimize");
    }

    #[test]
    fn test_valueless_tag_equivalence_to_wildcard() {
        // Value-less tag is equivalent to explicit wildcard
        let valueless = TaggedUrn::from_string("cap:ext").unwrap();
        let wildcard = TaggedUrn::from_string("cap:ext=*").unwrap();
        assert_eq!(valueless, wildcard);
        // Both serialize to value-less form
        assert_eq!(valueless.to_string(), "cap:ext");
        assert_eq!(wildcard.to_string(), "cap:ext");
    }

    #[test]
    fn test_valueless_tag_matching() {
        // Value-less tag (wildcard) matches any value
        let urn = TaggedUrn::from_string("cap:op=generate;ext").unwrap();

        let request_pdf = TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap();
        let request_docx = TaggedUrn::from_string("cap:op=generate;ext=docx").unwrap();
        let request_any = TaggedUrn::from_string("cap:op=generate;ext=anything").unwrap();

        assert!(urn.conforms_to(&request_pdf).unwrap());
        assert!(urn.conforms_to(&request_docx).unwrap());
        assert!(urn.conforms_to(&request_any).unwrap());
    }

    #[test]
    fn test_valueless_tag_in_pattern() {
        // Pattern with value-less tag (K=*) requires instance to have the tag
        let pattern = TaggedUrn::from_string("cap:op=generate;ext").unwrap();

        let instance_pdf = TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap();
        let instance_docx = TaggedUrn::from_string("cap:op=generate;ext=docx").unwrap();
        let instance_missing = TaggedUrn::from_string("cap:op=generate").unwrap();

        // NEW SEMANTICS: K=* (valueless tag) means must-have-any
        assert!(instance_pdf.conforms_to(&pattern).unwrap()); // Has ext=pdf
        assert!(instance_docx.conforms_to(&pattern).unwrap()); // Has ext=docx
        assert!(!instance_missing.conforms_to(&pattern).unwrap()); // Missing ext, pattern requires it

        // To accept missing ext, use ? instead
        let pattern_optional = TaggedUrn::from_string("cap:op=generate;ext=?").unwrap();
        assert!(instance_missing.conforms_to(&pattern_optional).unwrap());
    }

    #[test]
    fn test_valueless_tag_specificity() {
        // NEW GRADED SPECIFICITY:
        // K=v (exact): 3, K=* (must-have-any): 2, K=! (must-not): 1, K=? (unspecified): 0

        let urn1 = TaggedUrn::from_string("cap:op=generate").unwrap();
        let urn2 = TaggedUrn::from_string("cap:op=generate;optimize").unwrap(); // optimize = *
        let urn3 = TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap();

        assert_eq!(urn1.specificity(), 3);  // 1 exact = 3
        assert_eq!(urn2.specificity(), 5);  // 1 exact + 1 * = 3 + 2 = 5
        assert_eq!(urn3.specificity(), 6);  // 2 exact = 3 + 3 = 6
    }

    #[test]
    fn test_valueless_tag_roundtrip() {
        // Round-trip parsing and serialization
        let original = "cap:ext=pdf;op=generate;optimize;secure";
        let urn = TaggedUrn::from_string(original).unwrap();
        let serialized = urn.to_string();
        let reparsed = TaggedUrn::from_string(&serialized).unwrap();
        assert_eq!(urn, reparsed);
        assert_eq!(serialized, original);
    }

    #[test]
    fn test_valueless_tag_case_normalization() {
        // Value-less tags are normalized to lowercase like other keys
        let urn = TaggedUrn::from_string("cap:OPTIMIZE;Fast;SECURE").unwrap();
        assert_eq!(urn.get_tag("optimize"), Some(&"*".to_string()));
        assert_eq!(urn.get_tag("fast"), Some(&"*".to_string()));
        assert_eq!(urn.get_tag("secure"), Some(&"*".to_string()));
        assert_eq!(urn.to_string(), "cap:fast;optimize;secure");
    }

    #[test]
    fn test_empty_value_still_error() {
        // Empty value with = is still an error (different from value-less)
        assert!(TaggedUrn::from_string("cap:key=").is_err());
        assert!(TaggedUrn::from_string("cap:key=;other=value").is_err());
    }

    #[test]
    fn test_valueless_tag_compatibility() {
        // Value-less tags are compatible with any value
        let urn1 = TaggedUrn::from_string("cap:op=generate;ext").unwrap();
        let urn2 = TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap();
        let urn3 = TaggedUrn::from_string("cap:op=generate;ext=docx").unwrap();

        assert!(urn1.is_compatible_with(&urn2).unwrap());
        assert!(urn1.is_compatible_with(&urn3).unwrap());
        // But urn2 and urn3 are not compatible (different specific values)
        assert!(!urn2.is_compatible_with(&urn3).unwrap());
    }

    #[test]
    fn test_valueless_numeric_key_still_rejected() {
        // Purely numeric keys are still rejected for value-less tags
        assert!(TaggedUrn::from_string("cap:123").is_err());
        assert!(TaggedUrn::from_string("cap:op=generate;456").is_err());
    }

    #[test]
    fn test_whitespace_in_input_rejected() {
        // Leading whitespace fails hard
        let result = TaggedUrn::from_string(" cap:op=test");
        assert!(result.is_err());
        if let Err(TaggedUrnError::WhitespaceInInput(_)) = result {
            // Expected
        } else {
            panic!("Expected WhitespaceInInput error, got {:?}", result);
        }

        // Trailing whitespace fails hard
        let result = TaggedUrn::from_string("cap:op=test ");
        assert!(result.is_err());
        if let Err(TaggedUrnError::WhitespaceInInput(_)) = result {
            // Expected
        } else {
            panic!("Expected WhitespaceInInput error, got {:?}", result);
        }

        // Both leading and trailing whitespace fails hard
        let result = TaggedUrn::from_string(" cap:op=test ");
        assert!(result.is_err());
        if let Err(TaggedUrnError::WhitespaceInInput(_)) = result {
            // Expected
        } else {
            panic!("Expected WhitespaceInInput error, got {:?}", result);
        }

        // Tab and newline also count as whitespace
        assert!(TaggedUrn::from_string("\tcap:op=test").is_err());
        assert!(TaggedUrn::from_string("cap:op=test\n").is_err());

        // Clean input works
        assert!(TaggedUrn::from_string("cap:op=test").is_ok());
    }

    // ============================================================================
    // NEW SEMANTICS TESTS: ? (unspecified) and ! (must-not-have)
    // ============================================================================

    #[test]
    fn test_unspecified_question_mark_parsing() {
        // ? parses as unspecified
        let urn = TaggedUrn::from_string("cap:ext=?").unwrap();
        assert_eq!(urn.get_tag("ext"), Some(&"?".to_string()));
        // Serializes as key=?
        assert_eq!(urn.to_string(), "cap:ext=?");
    }

    #[test]
    fn test_must_not_have_exclamation_parsing() {
        // ! parses as must-not-have
        let urn = TaggedUrn::from_string("cap:ext=!").unwrap();
        assert_eq!(urn.get_tag("ext"), Some(&"!".to_string()));
        // Serializes as key=!
        assert_eq!(urn.to_string(), "cap:ext=!");
    }

    #[test]
    fn test_question_mark_pattern_matches_anything() {
        // Pattern with K=? matches any instance (with or without K)
        let pattern = TaggedUrn::from_string("cap:ext=?").unwrap();

        let instance_pdf = TaggedUrn::from_string("cap:ext=pdf").unwrap();
        let instance_docx = TaggedUrn::from_string("cap:ext=docx").unwrap();
        let instance_missing = TaggedUrn::from_string("cap:").unwrap();
        let instance_wildcard = TaggedUrn::from_string("cap:ext=*").unwrap();
        let instance_must_not = TaggedUrn::from_string("cap:ext=!").unwrap();

        assert!(instance_pdf.conforms_to(&pattern).unwrap(), "ext=pdf should match ext=?");
        assert!(instance_docx.conforms_to(&pattern).unwrap(), "ext=docx should match ext=?");
        assert!(instance_missing.conforms_to(&pattern).unwrap(), "(no ext) should match ext=?");
        assert!(instance_wildcard.conforms_to(&pattern).unwrap(), "ext=* should match ext=?");
        assert!(instance_must_not.conforms_to(&pattern).unwrap(), "ext=! should match ext=?");
    }

    #[test]
    fn test_question_mark_in_instance() {
        // Instance with K=? matches any pattern constraint
        let instance = TaggedUrn::from_string("cap:ext=?").unwrap();

        let pattern_pdf = TaggedUrn::from_string("cap:ext=pdf").unwrap();
        let pattern_wildcard = TaggedUrn::from_string("cap:ext=*").unwrap();
        let pattern_must_not = TaggedUrn::from_string("cap:ext=!").unwrap();
        let pattern_question = TaggedUrn::from_string("cap:ext=?").unwrap();
        let pattern_missing = TaggedUrn::from_string("cap:").unwrap();

        assert!(instance.conforms_to(&pattern_pdf).unwrap(), "ext=? should match ext=pdf");
        assert!(instance.conforms_to(&pattern_wildcard).unwrap(), "ext=? should match ext=*");
        assert!(instance.conforms_to(&pattern_must_not).unwrap(), "ext=? should match ext=!");
        assert!(instance.conforms_to(&pattern_question).unwrap(), "ext=? should match ext=?");
        assert!(instance.conforms_to(&pattern_missing).unwrap(), "ext=? should match (no ext)");
    }

    #[test]
    fn test_must_not_have_pattern_requires_absent() {
        // Pattern with K=! requires instance to NOT have K
        let pattern = TaggedUrn::from_string("cap:ext=!").unwrap();

        let instance_missing = TaggedUrn::from_string("cap:").unwrap();
        let instance_pdf = TaggedUrn::from_string("cap:ext=pdf").unwrap();
        let instance_wildcard = TaggedUrn::from_string("cap:ext=*").unwrap();
        let instance_must_not = TaggedUrn::from_string("cap:ext=!").unwrap();

        assert!(instance_missing.conforms_to(&pattern).unwrap(), "(no ext) should match ext=!");
        assert!(!instance_pdf.conforms_to(&pattern).unwrap(), "ext=pdf should NOT match ext=!");
        assert!(!instance_wildcard.conforms_to(&pattern).unwrap(), "ext=* should NOT match ext=!");
        assert!(instance_must_not.conforms_to(&pattern).unwrap(), "ext=! should match ext=!");
    }

    #[test]
    fn test_must_not_have_in_instance() {
        // Instance with K=! conflicts with patterns requiring K
        let instance = TaggedUrn::from_string("cap:ext=!").unwrap();

        let pattern_pdf = TaggedUrn::from_string("cap:ext=pdf").unwrap();
        let pattern_wildcard = TaggedUrn::from_string("cap:ext=*").unwrap();
        let pattern_must_not = TaggedUrn::from_string("cap:ext=!").unwrap();
        let pattern_question = TaggedUrn::from_string("cap:ext=?").unwrap();
        let pattern_missing = TaggedUrn::from_string("cap:").unwrap();

        assert!(!instance.conforms_to(&pattern_pdf).unwrap(), "ext=! should NOT match ext=pdf");
        assert!(!instance.conforms_to(&pattern_wildcard).unwrap(), "ext=! should NOT match ext=*");
        assert!(instance.conforms_to(&pattern_must_not).unwrap(), "ext=! should match ext=!");
        assert!(instance.conforms_to(&pattern_question).unwrap(), "ext=! should match ext=?");
        assert!(instance.conforms_to(&pattern_missing).unwrap(), "ext=! should match (no ext)");
    }

    #[test]
    fn test_full_cross_product_matching() {
        // Comprehensive test of all instance/pattern combinations
        // Based on the truth table in the plan

        // Helper to test a single case
        fn check(instance: &str, pattern: &str, expected: bool, msg: &str) {
            let inst = TaggedUrn::from_string(instance).unwrap();
            let patt = TaggedUrn::from_string(pattern).unwrap();
            assert_eq!(
                inst.conforms_to(&patt).unwrap(),
                expected,
                "{}: instance={}, pattern={}",
                msg,
                instance,
                pattern
            );
        }

        // Instance missing, Pattern variations
        check("cap:", "cap:", true, "(none)/(none)");
        check("cap:", "cap:k=?", true, "(none)/K=?");
        check("cap:", "cap:k=!", true, "(none)/K=!");
        check("cap:", "cap:k", false, "(none)/K=*");  // K is valueless = *
        check("cap:", "cap:k=v", false, "(none)/K=v");

        // Instance K=?, Pattern variations
        check("cap:k=?", "cap:", true, "K=?/(none)");
        check("cap:k=?", "cap:k=?", true, "K=?/K=?");
        check("cap:k=?", "cap:k=!", true, "K=?/K=!");
        check("cap:k=?", "cap:k", true, "K=?/K=*");
        check("cap:k=?", "cap:k=v", true, "K=?/K=v");

        // Instance K=!, Pattern variations
        check("cap:k=!", "cap:", true, "K=!/(none)");
        check("cap:k=!", "cap:k=?", true, "K=!/K=?");
        check("cap:k=!", "cap:k=!", true, "K=!/K=!");
        check("cap:k=!", "cap:k", false, "K=!/K=*");
        check("cap:k=!", "cap:k=v", false, "K=!/K=v");

        // Instance K=*, Pattern variations
        check("cap:k", "cap:", true, "K=*/(none)");
        check("cap:k", "cap:k=?", true, "K=*/K=?");
        check("cap:k", "cap:k=!", false, "K=*/K=!");
        check("cap:k", "cap:k", true, "K=*/K=*");
        check("cap:k", "cap:k=v", true, "K=*/K=v");

        // Instance K=v, Pattern variations
        check("cap:k=v", "cap:", true, "K=v/(none)");
        check("cap:k=v", "cap:k=?", true, "K=v/K=?");
        check("cap:k=v", "cap:k=!", false, "K=v/K=!");
        check("cap:k=v", "cap:k", true, "K=v/K=*");
        check("cap:k=v", "cap:k=v", true, "K=v/K=v");
        check("cap:k=v", "cap:k=w", false, "K=v/K=w");
    }

    #[test]
    fn test_mixed_special_values() {
        // Test URNs with multiple special values
        let pattern = TaggedUrn::from_string("cap:required;optional=?;forbidden=!;exact=pdf").unwrap();

        // Instance that satisfies all constraints
        let good_instance = TaggedUrn::from_string("cap:required=yes;optional=maybe;exact=pdf").unwrap();
        assert!(good_instance.conforms_to(&pattern).unwrap());

        // Instance missing required tag
        let missing_required = TaggedUrn::from_string("cap:optional=maybe;exact=pdf").unwrap();
        assert!(!missing_required.conforms_to(&pattern).unwrap());

        // Instance has forbidden tag
        let has_forbidden = TaggedUrn::from_string("cap:required=yes;forbidden=oops;exact=pdf").unwrap();
        assert!(!has_forbidden.conforms_to(&pattern).unwrap());

        // Instance with wrong exact value
        let wrong_exact = TaggedUrn::from_string("cap:required=yes;exact=doc").unwrap();
        assert!(!wrong_exact.conforms_to(&pattern).unwrap());
    }

    #[test]
    fn test_serialization_round_trip_special_values() {
        // All special values round-trip correctly
        let originals = [
            "cap:ext=?",
            "cap:ext=!",
            "cap:ext",  // * serializes as valueless
            "cap:a=?;b=!;c;d=exact",
        ];

        for original in originals {
            let urn = TaggedUrn::from_string(original).unwrap();
            let serialized = urn.to_string();
            let reparsed = TaggedUrn::from_string(&serialized).unwrap();
            assert_eq!(urn, reparsed, "Round-trip failed for: {}", original);
        }
    }

    #[test]
    fn test_compatibility_with_special_values() {
        // ! is incompatible with * and specific values
        let must_not = TaggedUrn::from_string("cap:ext=!").unwrap();
        let must_have = TaggedUrn::from_string("cap:ext=*").unwrap();
        let specific = TaggedUrn::from_string("cap:ext=pdf").unwrap();
        let unspecified = TaggedUrn::from_string("cap:ext=?").unwrap();
        let missing = TaggedUrn::from_string("cap:").unwrap();

        assert!(!must_not.is_compatible_with(&must_have).unwrap());
        assert!(!must_not.is_compatible_with(&specific).unwrap());
        assert!(must_not.is_compatible_with(&unspecified).unwrap());
        assert!(must_not.is_compatible_with(&missing).unwrap());
        assert!(must_not.is_compatible_with(&must_not).unwrap());

        // * is compatible with specific values
        assert!(must_have.is_compatible_with(&specific).unwrap());
        assert!(must_have.is_compatible_with(&must_have).unwrap());

        // ? is compatible with everything
        assert!(unspecified.is_compatible_with(&must_not).unwrap());
        assert!(unspecified.is_compatible_with(&must_have).unwrap());
        assert!(unspecified.is_compatible_with(&specific).unwrap());
        assert!(unspecified.is_compatible_with(&unspecified).unwrap());
        assert!(unspecified.is_compatible_with(&missing).unwrap());
    }

    #[test]
    fn test_specificity_with_special_values() {
        // Verify graded specificity scoring
        let exact = TaggedUrn::from_string("cap:a=x;b=y;c=z").unwrap(); // 3*3 = 9
        let must_have = TaggedUrn::from_string("cap:a;b;c").unwrap(); // 3*2 = 6
        let must_not = TaggedUrn::from_string("cap:a=!;b=!;c=!").unwrap(); // 3*1 = 3
        let unspecified = TaggedUrn::from_string("cap:a=?;b=?;c=?").unwrap(); // 3*0 = 0
        let mixed = TaggedUrn::from_string("cap:a=x;b;c=!;d=?").unwrap(); // 3+2+1+0 = 6

        assert_eq!(exact.specificity(), 9);
        assert_eq!(must_have.specificity(), 6);
        assert_eq!(must_not.specificity(), 3);
        assert_eq!(unspecified.specificity(), 0);
        assert_eq!(mixed.specificity(), 6);

        // Test specificity tuples
        assert_eq!(exact.specificity_tuple(), (3, 0, 0));
        assert_eq!(must_have.specificity_tuple(), (0, 3, 0));
        assert_eq!(must_not.specificity_tuple(), (0, 0, 3));
        assert_eq!(unspecified.specificity_tuple(), (0, 0, 0));
        assert_eq!(mixed.specificity_tuple(), (1, 1, 1));
    }
}
