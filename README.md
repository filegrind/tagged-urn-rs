# Tagged URN - Rust Implementation

A tagged URN system with flat tag-based naming, wildcard support, and specificity comparison.

## Overview

Tagged URN provides a formal system for tag-based identifiers with matching and comparison capabilities. It uses a flat key-value tag format that supports wildcards, specificity ranking, and flexible matching.

## Features

- **Flat Tag Format** - Simple `key=value` pairs separated by semicolons
- **Case Insensitive** - All input normalized to lowercase (except quoted values)
- **Tag Order Independent** - Canonical alphabetical sorting
- **Wildcard Support** - `*` matching in values only
- **Specificity Comparison** - More specific URNs are preferred
- **Smart Quoting** - Automatic quoting for special characters and case preservation

## Format

Tagged URNs use a flat tag-based format: `cap:tag1=value1;tag2=value2;tag3=value3`

**Examples:**
```
cap:op=extract;target=metadata;ext=pdf
cap:type=image;format=png;quality=high
cap:op=generate;target=thumbnail;output=binary
```

**Wildcards:**
- Use `*` to match any value: `cap:op=extract;format=*`
- Wildcards enable flexible matching

**Specificity:**
- More specific URNs are preferred over general ones
- `cap:op=extract;ext=pdf` is more specific than `cap:op=extract`

## Usage

```rust
use tagged_urn::{TaggedUrn, TaggedUrnBuilder};

// Create from string
let urn = TaggedUrn::from_string("cap:op=extract;target=metadata")?;

// Build with builder pattern
let urn = TaggedUrnBuilder::new()
    .tag("op", "extract")
    .tag("target", "metadata")
    .tag("ext", "pdf")
    .build()?;

// Check matching
let request = TaggedUrn::from_string("cap:op=extract")?;
if urn.matches(&request) {
    println!("URN matches request");
}

// Compare specificity
if urn.is_more_specific_than(&request) {
    println!("URN is more specific");
}
```

## Key Operations

### Matching

```rust
let urn = TaggedUrn::from_string("cap:op=extract;target=metadata;ext=pdf")?;
let request = TaggedUrn::from_string("cap:op=extract")?;

if urn.matches(&request) {
    println!("URN can handle this request");
}
```

### Specificity Comparison

```rust
let general = TaggedUrn::from_string("cap:op=extract")?;
let specific = TaggedUrn::from_string("cap:op=extract;ext=pdf")?;

if specific.is_more_specific_than(&general) {
    println!("Specific URN preferred");
}
```

### Builder Pattern

```rust
let urn = TaggedUrnBuilder::new()
    .tag("type", "inference")
    .tag("op", "conversation")
    .tag("language", "en")
    .build()?;
```

## Cross-Language Compatibility

This Rust implementation produces identical results to:
- [Go implementation](../tagged-urn-go/)
- [JavaScript implementation](../tagged-urn-js/)
- [Objective-C implementation](../tagged-urn-objc/)

All implementations pass the same test cases and follow identical rules.

## Testing

```bash
cargo test
```

## Documentation

See [RULES.md](docs/RULES.md) for the definitive specification of Tagged URN format, syntax, and behavior.

## Dependencies

- `serde` - Serialization/deserialization
- `serde_json` - JSON support
- `regex` - Pattern validation

## License

MIT License
