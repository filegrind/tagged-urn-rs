# Tagged URN Rules

## Definitive specification for Tagged URN format and behavior

### 1. Case Handling
- **Tag keys:** Always normalized to lowercase
- **Unquoted values:** Normalized to lowercase
- **Quoted values:** Case is preserved exactly as specified
- Example: `cap:key=VALUE` stores `{key: "value"}` (lowercase)
- Example: `cap:key="VALUE"` stores `{key: "VALUE"}` (preserved)

### 2. Tag Order Independence
The order of tags in the URN string does not matter. Tags are always sorted alphabetically by key in canonical form.

### 3. Mandatory Prefix
Tagged URNs must always be preceded by `cap:` which is the signifier of a tagged URN. The prefix is case-insensitive for parsing (`CAP:`, `Cap:`, `cap:` are all accepted) but always lowercase in canonical form.

### 4. Tag Separator
Tags are separated by semicolons (`;`).

### 5. Trailing Semicolon Optional
Presence or absence of the final trailing semicolon does not matter. Both `cap:key=value` and `cap:key=value;` are equivalent.

### 6. Character Restrictions

**Unquoted values:**
- Allowed characters in tag keys: alphanumeric, dashes (`-`), underscores (`_`), slashes (`/`), colons (`:`), dots (`.`)
- Allowed characters in unquoted values: same as keys plus special pattern characters (`*`, `?`, `!`)
- No spaces, quotes, semicolons, equals signs, or backslashes in unquoted values

**Quoted values:**
- Values may be enclosed in double quotes: `key="value"`
- ANY character is allowed inside quoted values (including spaces, semicolons, equals signs)
- Escape sequences inside quotes: `\"` for literal quote, `\\` for literal backslash
- Only `\"` and `\\` are valid escape sequences; other backslash sequences are errors
- Example: `cap:key="value with spaces"` is valid
- Example: `cap:key="value;with=special"` is valid
- Example: `cap:key="quote: \"hello\""` stores `quote: "hello"`

### 7. Tag Structure
- Tag separator within a tag: `=` separates tag key from tag value
- Tag separator between tags: `;` separates key-value pairs
- After the initial `cap:` prefix, colons (`:`) are treated as normal characters, not separators

### 8. No Special Tags
No reserved tag names - anything goes for tag keys.

### 9. Canonical Form and Serialization
- Tags are sorted alphabetically by key
- No final trailing semicolon
- Tag keys are always lowercase
- **Smart quoting on serialization:** Values are quoted only when necessary:
  - Quote if value contains special characters: `;`, `=`, `"`, `\`, or space
  - Quote if value contains any uppercase characters (to preserve case on round-trip)
  - Simple lowercase-only values are serialized without quotes
- Examples:
  - `{key: "simple"}` serializes to `cap:key=simple`
  - `{key: "Has Upper"}` serializes to `cap:key="Has Upper"`
  - `{key: "has;special"}` serializes to `cap:key="has;special"`

### 10. Special Pattern Values
The following special values control matching behavior:

| Value | Name | Meaning |
|-------|------|---------|
| `K=v` | Exact value | Must have key K with exact value v |
| `K=*` | Must-have-any | Must have key K with any value (presence required) |
| `K=!` | Must-not-have | Must NOT have key K (absence required) |
| `K=?` | Unspecified | No constraint on key K (explicit don't-care) |
| (missing) | No constraint | Same as `K=?` - key doesn't participate in matching |

- Special values `*`, `?`, and `!` are accepted only in tag values, not keys
- These values work symmetrically on both instance and pattern sides

### 11. Value-less Tags (Must-Have-Any)
- Tags may be specified without a value: `cap:key1=value1;optimize;key2=value2`
- A value-less tag like `optimize` is equivalent to `optimize=*` (must-have-any)
- This asserts that the tag MUST be present (with any value)
- **Parsing:** `tag` (no `=`) is parsed as `tag=*`
- **Serialization:** `tag=*` is serialized as just `tag` (no `=*`)
- **Note:** `tag=` (explicit `=` with no value) is still an error

## Matching Semantics (CRITICAL)

This section defines how Tagged URN matching works when comparing URNs. This is the core algorithm that ALL implementations MUST follow exactly.

### 12. Per-Tag Value Matching

Matching is symmetric - special values work the same on both instance and pattern sides.

**Truth Table:**
| Instance | Pattern | Match? | Reason |
|----------|---------|--------|--------|
| (none) | (none) | OK | No constraint either side |
| (none) | K=? | OK | Pattern doesn't care |
| (none) | K=! | OK | Pattern wants absent, it is |
| (none) | K=* | NO | Pattern wants present |
| (none) | K=v | NO | Pattern wants exact value |
| K=? | (any) | OK | Instance doesn't care |
| K=! | (none) | OK | Symmetric: both absent |
| K=! | K=? | OK | Pattern doesn't care |
| K=! | K=! | OK | Both want absent |
| K=! | K=* | NO | Conflict: absent vs present |
| K=! | K=v | NO | Conflict: absent vs value |
| K=* | (none) | OK | Pattern has no constraint |
| K=* | K=? | OK | Pattern doesn't care |
| K=* | K=! | NO | Conflict: present vs absent |
| K=* | K=* | OK | Both accept any presence |
| K=* | K=v | OK | Instance accepts any, v is fine |
| K=v | (none) | OK | Pattern has no constraint |
| K=v | K=? | OK | Pattern doesn't care |
| K=v | K=! | NO | Conflict: value vs absent |
| K=v | K=* | OK | Pattern wants any, v satisfies |
| K=v | K=v | OK | Exact match |
| K=v | K=w | NO | Value mismatch (v≠w) |

### 13. Matching: `conforms_to` and `accepts`

Matching is **directional** — it matters which URN is the pattern and which is the instance.
Two methods make this explicit:

- `instance.conforms_to(pattern)` — does the instance satisfy the pattern's constraints?
- `pattern.accepts(instance)` — does the pattern accept this instance?

These are equivalent: `a.conforms_to(b)` = `b.accepts(a)`.

Given an **instance** and a **pattern**, the instance conforms to the pattern if and only if:

1. Collect all keys from both instance and pattern
2. For each key, check if the values match using the truth table above
3. If all keys match, return true; otherwise return false

```rust
pub fn conforms_to(&self, pattern: &TaggedUrn) -> Result<bool, TaggedUrnError> {
    // Prefixes must match
    if self.prefix != pattern.prefix {
        return Err(TaggedUrnError::PrefixMismatch { ... });
    }

    // Check all keys from both sides
    let all_keys: HashSet<&String> = self.tags.keys()
        .chain(pattern.tags.keys())
        .collect();

    for key in all_keys {
        let inst = self.tags.get(key).map(|s| s.as_str());
        let patt = pattern.tags.get(key).map(|s| s.as_str());

        if !values_match(inst, patt) {
            return Ok(false);
        }
    }
    Ok(true)
}
```

### 14. Matching Examples

```
# Example 1: Exact match
Instance: cap:op=generate;ext=pdf
Pattern:  cap:op=generate;ext=pdf
Result:   MATCH

# Example 2: Pattern has no constraint on ext
Instance: cap:op=generate;ext=pdf
Pattern:  cap:op=generate
Result:   MATCH (missing tag = no constraint)

# Example 3: Instance has extra tags
Instance: cap:op=generate;ext=pdf;version=2
Pattern:  cap:op=generate;ext=pdf
Result:   MATCH (pattern doesn't constrain version)

# Example 4: Pattern uses must-have-any
Instance: cap:op=generate;ext=pdf
Pattern:  cap:op=generate;ext=*
Result:   MATCH (instance has ext, pattern just wants any ext)

# Example 5: Value mismatch
Instance: cap:op=generate;ext=pdf
Pattern:  cap:op=generate;ext=docx
Result:   NO MATCH (pdf ≠ docx)

# Example 6: Must-not-have satisfied
Instance: cap:op=generate
Pattern:  cap:op=generate;debug=!
Result:   MATCH (instance lacks debug, pattern wants it absent)

# Example 7: Must-not-have violated
Instance: cap:op=generate;debug=true
Pattern:  cap:op=generate;debug=!
Result:   NO MATCH (instance has debug, pattern wants it absent)

# Example 8: Must-have-any not satisfied
Instance: cap:op=generate
Pattern:  cap:op=generate;ext=*
Result:   NO MATCH (instance lacks ext, pattern requires it)

# Example 9: Explicit unspecified
Instance: cap:op=generate;ext=pdf
Pattern:  cap:op=generate;ext=?
Result:   MATCH (pattern explicitly doesn't care about ext)

# Example 10: Value-less tag (must-have-any)
Instance: cap:op=generate;ext=pdf
Pattern:  cap:op=generate;ext           (ext = ext=*)
Result:   MATCH (instance has ext with value)
```

### 15. Graded Specificity
When multiple URNs match a request, select the one with highest specificity using graded scoring:

| Value Type | Score | Example |
|------------|-------|---------|
| Exact value (K=v) | 3 | `ext=pdf` |
| Must-have-any (K=*) | 2 | `ext=*` or `ext` |
| Must-not-have (K=!) | 1 | `debug=!` |
| Unspecified (K=?) | 0 | `ext=?` or missing |

**Total specificity** = sum of all tag scores

Examples:
- `cap:op=generate;ext=pdf` → 3 + 3 = 6
- `cap:op=generate;ext=*` → 3 + 2 = 5
- `cap:op=generate;ext` → 3 + 2 = 5 (value-less = must-have-any)
- `cap:op=generate` → 3

**Tie-breaking:** Compare tuples `(exact_count, must_have_any_count, must_not_count)` lexicographically.

### 16. Selection Algorithm
1. Collect all URNs that match the request
2. Calculate graded specificity for each
3. Select the one with highest specificity
4. If tie, use specificity tuple; if still tied, first registered wins

### 17. Symmetric Matching
The matching is symmetric - special values work the same on both sides:

**Instance with wildcards:**
```
Instance: cap:ext=*        Pattern: cap:ext=pdf    → MATCH (instance accepts any)
Instance: cap:ext=*        Pattern: cap:ext=!      → NO MATCH (conflict: present vs absent)
```

**Instance with must-not-have:**
```
Instance: cap:debug=!      Pattern: cap:debug=!    → MATCH (both want absent)
Instance: cap:debug=!      Pattern: cap:debug=true → NO MATCH (conflict: absent vs value)
```

### 18. Duplicate Keys
Duplicate keys in the same URN result in an error - last occurrence does not win.

### 19. UTF-8 Support
Full UTF-8 character support within the allowed character set restrictions.

### 20. Numeric Values
- Tag keys cannot be pure numeric
- Tag values can be pure numeric

### 21. Empty Tagged URN
`cap:` with no tags is valid and represents no constraints (matches any URN with the same prefix).

### 22. Length Restrictions
No explicit length restrictions, though practical limits exist based on URL and system constraints (typically ~2000 characters).

### 23. Special Value Restrictions
Special pattern characters (`*`, `?`, `!`) are only valid in tag values, not in tag keys. These characters have specific matching semantics and cannot be used as literal values without quoting.

### 24. Colon Treatment
Forward slashes (`/`) and colons (`:`) are valid anywhere in tag components and treated as normal characters, except for the mandatory `cap:` prefix which is not part of the tag structure.

### 25. Quote Errors
- **Unterminated Quote:** A quoted value that starts with `"` but never closes is an error
- **Invalid Escape Sequence:** Inside a quoted value, `\` followed by anything other than `"` or `\` is an error
- Examples of errors:
  - `cap:key="unterminated` → UnterminatedQuote error
  - `cap:key="bad\n"` → InvalidEscapeSequence error (only `\"` and `\\` allowed)

### 26. Semantic Equivalence
- `cap:key=simple` and `cap:key="simple"` both parse to `{key: "simple"}` (lowercase)
- `cap:key="Simple"` parses to `{key: "Simple"}` (preserved) - NOT equal to unquoted
- The quoting information is not stored; serialization re-determines quoting based on value content

## Implementation Notes

- All implementations must normalize tag keys to lowercase
- All implementations must normalize unquoted values to lowercase
- All implementations must preserve case in quoted values
- All implementations must sort tags alphabetically in canonical output
- All implementations must handle trailing semicolons consistently
- All implementations must validate character restrictions identically
- All implementations must implement matching logic identically per the truth table
- All implementations must reject duplicate keys with appropriate error messages
- All implementations must use state-machine parsing for quoted value support
- All implementations must implement smart quoting on serialization
- All implementations must parse value-less tags as must-have-any (`tag` → `tag=*`)
- All implementations must serialize must-have-any tags as value-less (`tag=*` → `tag`)
- All implementations must serialize `?` and `!` explicitly (`tag=?`, `tag=!`)
- All implementations must implement graded specificity scoring
- All implementations must allow `?` and `!` as unquoted values

## Error Codes (Consistent Across All Implementations)

| Code | Name | Description |
|------|------|-------------|
| 1 | InvalidFormat | Empty or malformed URN |
| 2 | EmptyTag | Empty key or value component |
| 3 | InvalidCharacter | Disallowed character in key/value |
| 4 | InvalidTagFormat | Tag not in key=value format |
| 5 | MissingCapPrefix | URN does not start with `cap:` |
| 6 | DuplicateKey | Same key appears twice |
| 7 | NumericKey | Key is purely numeric |
| 8 | UnterminatedQuote | Quoted value never closed |
| 9 | InvalidEscapeSequence | Invalid escape in quoted value |
