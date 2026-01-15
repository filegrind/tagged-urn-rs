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
                return Err(TaggedUrnError::InvalidTagFormat(format!(
                    "incomplete tag '{}'",
                    current_key
                )));
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
    pub fn to_string(&self) -> String {
        let tags_str = self
            .tags
            .iter()
            .map(|(k, v)| {
                if Self::needs_quoting(v) {
                    format!("{}={}", k, Self::quote_value(v))
                } else {
                    format!("{}={}", k, v)
                }
            })
            .collect::<Vec<_>>()
            .join(";");
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
    pub fn with_tag(mut self, key: String, value: String) -> Self {
        self.tags.insert(key.to_lowercase(), value);
        self
    }

    /// Remove a tag
    /// Key is normalized to lowercase for case-insensitive removal
    pub fn without_tag(mut self, key: &str) -> Self {
        self.tags.remove(&key.to_lowercase());
        self
    }

    /// Check if this URN matches another based on tag compatibility
    ///
    /// IMPORTANT: Both URNs must have the same prefix. Comparing URNs with
    /// different prefixes is a programming error and will return an error.
    ///
    /// A URN matches a request if:
    /// - Both have the same prefix
    /// - For each tag in the request: URN has same value, wildcard (*), or missing tag
    /// - For each tag in the URN: if request is missing that tag, that's fine (URN is more specific)
    /// Missing tags are treated as wildcards (less specific, can handle any value).
    pub fn matches(&self, request: &TaggedUrn) -> Result<bool, TaggedUrnError> {
        // First check prefix - must match exactly
        if self.prefix != request.prefix {
            return Err(TaggedUrnError::PrefixMismatch {
                expected: self.prefix.clone(),
                actual: request.prefix.clone(),
            });
        }

        // Check all tags that the request specifies
        for (request_key, request_value) in &request.tags {
            match self.tags.get(request_key) {
                Some(urn_value) => {
                    if urn_value == "*" {
                        // URN has wildcard - can handle any value
                        continue;
                    }
                    if request_value == "*" {
                        // Request accepts any value - URN's specific value matches
                        continue;
                    }
                    if urn_value != request_value {
                        // URN has specific value that doesn't match request's specific value
                        return Ok(false);
                    }
                }
                None => {
                    // Missing tag in URN is treated as wildcard - can handle any value
                    continue;
                }
            }
        }

        // If URN has additional specific tags that request doesn't specify, that's fine
        // The URN is just more specific than needed
        Ok(true)
    }

    pub fn matches_str(&self, request_str: &str) -> Result<bool, TaggedUrnError> {
        let request = TaggedUrn::from_string(request_str)?;
        self.matches(&request)
    }

    /// Check if this URN can handle a request
    ///
    /// This is used when a request comes in with a tagged URN
    /// and we need to see if this URN can fulfill it
    pub fn can_handle(&self, request: &TaggedUrn) -> Result<bool, TaggedUrnError> {
        self.matches(request)
    }

    /// Calculate specificity score for URN matching
    ///
    /// More specific URNs have higher scores and are preferred
    pub fn specificity(&self) -> usize {
        // Count non-wildcard tags
        self.tags.values().filter(|v| v.as_str() != "*").count()
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
    /// the same types of requests (considering wildcards and missing tags as wildcards)
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
            match (self.tags.get(&key), other.tags.get(&key)) {
                (Some(v1), Some(v2)) => {
                    // Both have the tag - they must match or one must be wildcard
                    if v1 != "*" && v2 != "*" && v1 != v2 {
                        return Ok(false);
                    }
                }
                (Some(_), None) | (None, Some(_)) => {
                    // One has the tag, the other doesn't - missing tag is wildcard, so compatible
                    continue;
                }
                (None, None) => {
                    // Neither has the tag - shouldn't happen in this loop
                    continue;
                }
            }
        }

        Ok(true)
    }

    /// Create a wildcard version by replacing specific values with wildcards
    pub fn with_wildcard_tag(mut self, key: &str) -> Self {
        if self.tags.contains_key(key) {
            self.tags.insert(key.to_string(), "*".to_string());
        }
        self
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
    /// Find the most specific URN that can handle a request
    /// All URNs must have the same prefix as the request
    pub fn find_best_match<'a>(urns: &'a [TaggedUrn], request: &TaggedUrn) -> Result<Option<&'a TaggedUrn>, TaggedUrnError> {
        let mut best: Option<&TaggedUrn> = None;
        let mut best_specificity = 0;

        for urn in urns {
            if urn.can_handle(request)? {
                let specificity = urn.specificity();
                if best.is_none() || specificity > best_specificity {
                    best = Some(urn);
                    best_specificity = specificity;
                }
            }
        }

        Ok(best)
    }

    /// Find all URNs that can handle a request, sorted by specificity
    /// All URNs must have the same prefix as the request
    pub fn find_all_matches<'a>(urns: &'a [TaggedUrn], request: &TaggedUrn) -> Result<Vec<&'a TaggedUrn>, TaggedUrnError> {
        let mut matches: Vec<&TaggedUrn> = Vec::new();

        for urn in urns {
            if urn.can_handle(request)? {
                matches.push(urn);
            }
        }

        // Sort by specificity (most specific first)
        matches.sort_by_key(|urn| std::cmp::Reverse(urn.specificity()));
        Ok(matches)
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
    pub fn tag(mut self, key: &str, value: &str) -> Self {
        self.tags.insert(key.to_lowercase(), value.to_string());
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

        let result = urn1.matches(&urn2);
        assert!(result.is_err());
        if let Err(TaggedUrnError::PrefixMismatch { expected, actual }) = result {
            assert_eq!(expected, "cap");
            assert_eq!(actual, "myapp");
        } else {
            panic!("Expected PrefixMismatch error");
        }
    }

    #[test]
    fn test_builder_with_prefix() {
        let urn = TaggedUrnBuilder::new("custom")
            .tag("key", "value")
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
        let urn = TaggedUrnBuilder::new("cap").tag("key", "simple").build().unwrap();
        assert_eq!(urn.to_string(), "cap:key=simple");

        // Value with spaces - needs quoting
        let urn2 = TaggedUrnBuilder::new("cap")
            .tag("key", "has spaces")
            .build()
            .unwrap();
        assert_eq!(urn2.to_string(), r#"cap:key="has spaces""#);

        // Value with semicolons - needs quoting
        let urn3 = TaggedUrnBuilder::new("cap")
            .tag("key", "has;semi")
            .build()
            .unwrap();
        assert_eq!(urn3.to_string(), r#"cap:key="has;semi""#);

        // Value with uppercase - needs quoting to preserve
        let urn4 = TaggedUrnBuilder::new("cap")
            .tag("key", "HasUpper")
            .build()
            .unwrap();
        assert_eq!(urn4.to_string(), r#"cap:key="HasUpper""#);

        // Value with quotes - needs quoting and escaping
        let urn5 = TaggedUrnBuilder::new("cap")
            .tag("key", r#"has"quote"#)
            .build()
            .unwrap();
        assert_eq!(urn5.to_string(), r#"cap:key="has\"quote""#);

        // Value with backslashes - needs quoting and escaping
        let urn6 = TaggedUrnBuilder::new("cap")
            .tag("key", r#"path\file"#)
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
        assert!(urn1.matches(&urn2).unwrap());
        assert!(urn2.matches(&urn1).unwrap());
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
        assert!(urn.matches(&request1).unwrap());

        // Subset match
        let request2 = TaggedUrn::from_string("cap:op=generate").unwrap();
        assert!(urn.matches(&request2).unwrap());

        // Wildcard request should match specific URN
        let request3 = TaggedUrn::from_string("cap:ext=*").unwrap();
        assert!(urn.matches(&request3).unwrap()); // URN has ext=pdf, request accepts any ext

        // No match - conflicting value
        let request4 = TaggedUrn::from_string("cap:op=extract").unwrap();
        assert!(!urn.matches(&request4).unwrap());
    }

    #[test]
    fn test_matching_case_sensitive_values() {
        // Values with different case should NOT match
        let urn1 = TaggedUrn::from_string(r#"cap:key="Value""#).unwrap();
        let urn2 = TaggedUrn::from_string(r#"cap:key="value""#).unwrap();
        assert!(!urn1.matches(&urn2).unwrap());
        assert!(!urn2.matches(&urn1).unwrap());

        // Same case should match
        let urn3 = TaggedUrn::from_string(r#"cap:key="Value""#).unwrap();
        assert!(urn1.matches(&urn3).unwrap());
    }

    #[test]
    fn test_missing_tag_handling() {
        let urn = TaggedUrn::from_string("cap:op=generate").unwrap();

        // Request with tag should match URN without tag (treated as wildcard)
        let request1 = TaggedUrn::from_string("cap:ext=pdf").unwrap();
        assert!(urn.matches(&request1).unwrap()); // URN missing ext tag = wildcard, can handle any ext

        // But URN with extra tags can match subset requests
        let urn2 = TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap();
        let request2 = TaggedUrn::from_string("cap:op=generate").unwrap();
        assert!(urn2.matches(&request2).unwrap());
    }

    #[test]
    fn test_specificity() {
        let urn1 = TaggedUrn::from_string("cap:type=general").unwrap();
        let urn2 = TaggedUrn::from_string("cap:op=generate").unwrap();
        let urn3 = TaggedUrn::from_string("cap:op=*;ext=pdf").unwrap();

        assert_eq!(urn1.specificity(), 1);
        assert_eq!(urn2.specificity(), 1);
        assert_eq!(urn3.specificity(), 1); // wildcard doesn't count

        assert!(!urn2.is_more_specific_than(&urn1).unwrap()); // Different tags, not compatible
    }

    #[test]
    fn test_builder() {
        let urn = TaggedUrnBuilder::new("cap")
            .tag("op", "generate")
            .tag("target", "thumbnail")
            .tag("ext", "pdf")
            .tag("output", "binary")
            .build()
            .unwrap();

        assert_eq!(urn.get_tag("op"), Some(&"generate".to_string()));
        assert_eq!(urn.get_tag("output"), Some(&"binary".to_string()));
    }

    #[test]
    fn test_builder_preserves_case() {
        let urn = TaggedUrnBuilder::new("cap")
            .tag("KEY", "ValueWithCase")
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
        let urn3 = TaggedUrn::from_string("cap:type=image;op=extract").unwrap();

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

        assert_eq!(wildcarded.to_string(), "cap:ext=*");

        // Test that wildcarded URN can match more requests
        let request = TaggedUrn::from_string("cap:ext=jpg").unwrap();
        assert!(!urn.matches(&request).unwrap());
        assert!(wildcarded.matches(&TaggedUrn::from_string("cap:ext=*").unwrap()).unwrap());
    }

    #[test]
    fn test_empty_tagged_urn() {
        // Empty tagged URN should be valid and match everything
        let empty_urn = TaggedUrn::from_string("cap:").unwrap();
        assert_eq!(empty_urn.tags.len(), 0);
        assert_eq!(empty_urn.to_string(), "cap:");

        // Should match any other URN with same prefix
        let specific_urn = TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap();
        assert!(empty_urn.matches(&specific_urn).unwrap());
        assert!(empty_urn.matches(&empty_urn).unwrap());

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
        let urn = TaggedUrn::empty("cap".to_string()).with_tag("key".to_string(), "ValueWithCase".to_string());
        assert_eq!(urn.get_tag("key"), Some(&"ValueWithCase".to_string()));
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
        assert!(urn.matches(&request).unwrap(), "Test 1: Exact match should succeed");
    }

    #[test]
    fn test_matching_semantics_test2_urn_missing_tag() {
        // Test 2: URN missing tag (implicit wildcard)
        // URN:     cap:op=generate
        // Request: cap:op=generate;ext=pdf
        // Result:  MATCH (URN can handle any ext)
        let urn = TaggedUrn::from_string("cap:op=generate").unwrap();
        let request = TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap();
        assert!(urn.matches(&request).unwrap(), "Test 2: URN missing tag should match (implicit wildcard)");
    }

    #[test]
    fn test_matching_semantics_test3_urn_has_extra_tag() {
        // Test 3: URN has extra tag
        // URN:     cap:op=generate;ext=pdf;version=2
        // Request: cap:op=generate;ext=pdf
        // Result:  MATCH (request doesn't constrain version)
        let urn = TaggedUrn::from_string("cap:op=generate;ext=pdf;version=2").unwrap();
        let request = TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap();
        assert!(urn.matches(&request).unwrap(), "Test 3: URN with extra tag should match");
    }

    #[test]
    fn test_matching_semantics_test4_request_has_wildcard() {
        // Test 4: Request has wildcard
        // URN:     cap:op=generate;ext=pdf
        // Request: cap:op=generate;ext=*
        // Result:  MATCH (request accepts any ext)
        let urn = TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap();
        let request = TaggedUrn::from_string("cap:op=generate;ext=*").unwrap();
        assert!(urn.matches(&request).unwrap(), "Test 4: Request wildcard should match");
    }

    #[test]
    fn test_matching_semantics_test5_urn_has_wildcard() {
        // Test 5: URN has wildcard
        // URN:     cap:op=generate;ext=*
        // Request: cap:op=generate;ext=pdf
        // Result:  MATCH (URN handles any ext)
        let urn = TaggedUrn::from_string("cap:op=generate;ext=*").unwrap();
        let request = TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap();
        assert!(urn.matches(&request).unwrap(), "Test 5: URN wildcard should match");
    }

    #[test]
    fn test_matching_semantics_test6_value_mismatch() {
        // Test 6: Value mismatch
        // URN:     cap:op=generate;ext=pdf
        // Request: cap:op=generate;ext=docx
        // Result:  NO MATCH
        let urn = TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap();
        let request = TaggedUrn::from_string("cap:op=generate;ext=docx").unwrap();
        assert!(!urn.matches(&request).unwrap(), "Test 6: Value mismatch should not match");
    }

    #[test]
    fn test_matching_semantics_test7_fallback_pattern() {
        // Test 7: Fallback pattern
        // URN:     cap:op=generate_thumbnail;out="media:type=binary;v=1"
        // Request: cap:op=generate_thumbnail;out="media:type=binary;v=1";ext=wav
        // Result:  MATCH (URN has implicit ext=*)
        let urn = TaggedUrn::from_string(r#"cap:op=generate_thumbnail;out="media:type=binary;v=1""#).unwrap();
        let request = TaggedUrn::from_string(r#"cap:op=generate_thumbnail;out="media:type=binary;v=1";ext=wav"#).unwrap();
        assert!(urn.matches(&request).unwrap(), "Test 7: Fallback pattern should match (URN missing ext = implicit wildcard)");
    }

    #[test]
    fn test_matching_semantics_test8_empty_urn_matches_anything() {
        // Test 8: Empty URN matches anything
        // URN:     cap:
        // Request: cap:op=generate;ext=pdf
        // Result:  MATCH
        let urn = TaggedUrn::from_string("cap:").unwrap();
        let request = TaggedUrn::from_string("cap:op=generate;ext=pdf").unwrap();
        assert!(urn.matches(&request).unwrap(), "Test 8: Empty URN should match anything");
    }

    #[test]
    fn test_matching_semantics_test9_cross_dimension_independence() {
        // Test 9: Cross-dimension independence
        // URN:     cap:op=generate
        // Request: cap:ext=pdf
        // Result:  MATCH (both have implicit wildcards for missing tags)
        let urn = TaggedUrn::from_string("cap:op=generate").unwrap();
        let request = TaggedUrn::from_string("cap:ext=pdf").unwrap();
        assert!(urn.matches(&request).unwrap(), "Test 9: Cross-dimension independence should match");
    }

    #[test]
    fn test_matching_different_prefixes_error() {
        // URNs with different prefixes should cause an error, not just return false
        let urn1 = TaggedUrn::from_string("cap:op=test").unwrap();
        let urn2 = TaggedUrn::from_string("other:op=test").unwrap();

        let result = urn1.matches(&urn2);
        assert!(result.is_err());

        let result2 = urn1.is_compatible_with(&urn2);
        assert!(result2.is_err());

        let result3 = urn1.is_more_specific_than(&urn2);
        assert!(result3.is_err());
    }
}
