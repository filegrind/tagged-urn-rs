# Rust Test Catalog

**Total Tests:** 96

**Numbered Tests:** 96

**Unnumbered Tests:** 0

**Numbered Tests Missing Descriptions:** 0

**Numbering Mismatches:** 0

All numbered test numbers are unique.

This catalog lists all tests in the Rust codebase.

| Test # | Function Name | Description | File |
|--------|---------------|-------------|------|
| test0001 | `test0001_tag_order_normalization` | TEST0001: Tag order normalization | src/tagged_urn.rs:3068 |
| test0501 | `test0501_tagged_urn_creation` | TEST0501: Create tagged URN from string and verify prefix and tag values | src/tagged_urn.rs:1466 |
| test0502 | `test0502_custom_prefix` | TEST0502: Parse URN with custom prefix and verify serialization | src/tagged_urn.rs:1476 |
| test0503 | `test0503_prefix_case_insensitive` | TEST0503: Normalize prefix to lowercase regardless of input case | src/tagged_urn.rs:1485 |
| test0504 | `test0504_prefix_mismatch_error` | TEST0504: Return PrefixMismatch error when comparing URNs with different prefixes | src/tagged_urn.rs:1502 |
| test0505 | `test0505_builder_with_prefix` | TEST0505: Build URN with custom prefix using TaggedUrnBuilder | src/tagged_urn.rs:1520 |
| test0506 | `test0506_unquoted_values_lowercased` | TEST0506: Normalize unquoted keys and values to lowercase | src/tagged_urn.rs:1532 |
| test0507 | `test0507_quoted_values_preserve_case` | TEST0507: Preserve original case for quoted values while lowercasing keys | src/tagged_urn.rs:1554 |
| test0508 | `test0508_quoted_value_special_chars` | TEST0508: Parse quoted values containing semicolons, equals signs, and spaces | src/tagged_urn.rs:1573 |
| test0509 | `test0509_quoted_value_escape_sequences` | TEST0509: Parse escape sequences for quotes and backslashes in quoted values | src/tagged_urn.rs:1589 |
| test0510 | `test0510_mixed_quoted_unquoted` | TEST0510: Parse URN with both quoted and unquoted tag values | src/tagged_urn.rs:1605 |
| test0511 | `test0511_unterminated_quote_error` | TEST0511: Reject unterminated quoted value with appropriate error | src/tagged_urn.rs:1613 |
| test0512 | `test0512_invalid_escape_sequence_error` | TEST0512: Reject invalid escape sequences in quoted values | src/tagged_urn.rs:1623 |
| test0513 | `test0513_serialization_smart_quoting` | TEST0513: Apply smart quoting during serialization based on value content | src/tagged_urn.rs:1640 |
| test0514 | `test0514_round_trip_simple` | TEST0514: Round-trip parse and serialize a simple URN | src/tagged_urn.rs:1686 |
| test0515 | `test0515_round_trip_quoted` | TEST0515: Round-trip parse and serialize a URN with quoted values | src/tagged_urn.rs:1696 |
| test0516 | `test0516_round_trip_escapes` | TEST0516: Round-trip parse and serialize a URN with escape sequences | src/tagged_urn.rs:1707 |
| test0517 | `test0517_prefix_required` | TEST0517: Require a prefix in URN string and reject missing prefix | src/tagged_urn.rs:1718 |
| test0518 | `test0518_trailing_semicolon_equivalence` | TEST0518: Treat trailing semicolon as equivalent to no trailing semicolon | src/tagged_urn.rs:1733 |
| test0519 | `test0519_canonical_string_format` | TEST0519: Serialize tags in alphabetical order as canonical string format | src/tagged_urn.rs:1765 |
| test0520 | `test0520_tag_matching` | TEST0520: Match tags with exact values, subsets, wildcards, and mismatches | src/tagged_urn.rs:1777 |
| test0521 | `test0521_matching_case_sensitive_values` | TEST0521: Enforce case-sensitive matching for quoted tag values | src/tagged_urn.rs:1800 |
| test0522 | `test0522_missing_tag_handling` | TEST0522: Handle missing tags in instance vs pattern matching semantics | src/tagged_urn.rs:1814 |
| test0523 | `test0523_specificity` | TEST0523: Compute graded specificity scores and tuples for URN tags | src/tagged_urn.rs:1842 |
| test0524 | `test0524_builder` | TEST0524: Build URN with multiple tags using TaggedUrnBuilder | src/tagged_urn.rs:1879 |
| test0525 | `test0525_builder_preserves_case` | TEST0525: Preserve value case in builder while lowercasing keys | src/tagged_urn.rs:1894 |
| test0526 | `test0526_directional_accepts_with_tag_overlap` | TEST0526: Verify directional accepts between patterns with shared and disjoint tags | src/tagged_urn.rs:1908 |
| test0527 | `test0527_best_match` | TEST0527: Find best matching URN by specificity from a list of candidates | src/tagged_urn.rs:1936 |
| test0528 | `test0528_merge_and_subset` | TEST0528: Merge two URNs and extract a subset of tags | src/tagged_urn.rs:1953 |
| test0529 | `test0529_merge_prefix_mismatch` | TEST0529: Reject merge of URNs with different prefixes | src/tagged_urn.rs:1970 |
| test0530 | `test0530_wildcard_tag` | TEST0530: Convert specific tag value to wildcard and verify matching behavior | src/tagged_urn.rs:1981 |
| test0531 | `test0531_empty_tagged_urn` | TEST0531: Handle empty tagged URN with no tags in matching and serialization | src/tagged_urn.rs:1996 |
| test0532 | `test0532_empty_with_custom_prefix` | TEST0532: Create empty URN with custom prefix | src/tagged_urn.rs:2026 |
| test0533 | `test0533_extended_character_support` | TEST0533: Parse forward slashes and colons in unquoted tag values | src/tagged_urn.rs:2035 |
| test0534 | `test0534_wildcard_restrictions` | TEST0534: Reject wildcard in keys but accept wildcard in values | src/tagged_urn.rs:2047 |
| test0535 | `test0535_duplicate_key_rejection` | TEST0535: Reject duplicate keys in URN string | src/tagged_urn.rs:2058 |
| test0536 | `test0536_numeric_key_restriction` | TEST0536: Reject purely numeric keys but allow mixed alphanumeric keys | src/tagged_urn.rs:2068 |
| test0537 | `test0537_empty_value_error` | TEST0537: Reject empty value after equals sign | src/tagged_urn.rs:2082 |
| test0538 | `test0538_has_tag_case_sensitive` | TEST0538: Verify has_tag uses case-sensitive value comparison and case-insensitive key lookup | src/tagged_urn.rs:2089 |
| test0539 | `test0539_with_tag_preserves_value` | TEST0539: Preserve value case when adding tag with with_tag method | src/tagged_urn.rs:2106 |
| test0540 | `test0540_with_tag_rejects_empty_value` | TEST0540: Reject empty value string in with_tag method | src/tagged_urn.rs:2113 |
| test0541 | `test0541_builder_rejects_empty_value` | TEST0541: Reject empty value string in builder tag method | src/tagged_urn.rs:2125 |
| test0542 | `test0542_semantic_equivalence` | TEST0542: Treat quoted and unquoted simple lowercase values as semantically equivalent | src/tagged_urn.rs:2137 |
| test0543 | `test0543_matching_semantics_test1_exact_match` | TEST0543: Verify exact match when instance and pattern have identical tags | src/tagged_urn.rs:2156 |
| test0544 | `test0544_matching_semantics_test2_instance_missing_tag` | TEST0544: Reject match when instance is missing a tag required by pattern | src/tagged_urn.rs:2168 |
| test0545 | `test0545_matching_semantics_test3_urn_has_extra_tag` | TEST0545: Match when instance has extra tags not constrained by pattern | src/tagged_urn.rs:2187 |
| test0546 | `test0546_matching_semantics_test4_request_has_wildcard` | TEST0546: Match when pattern has wildcard accepting any value for a tag | src/tagged_urn.rs:2199 |
| test0547 | `test0547_matching_semantics_test5_urn_has_wildcard` | TEST0547: Match when instance has wildcard satisfying pattern's specific value | src/tagged_urn.rs:2211 |
| test0548 | `test0548_matching_semantics_test6_value_mismatch` | TEST0548: Reject match when tag values conflict between instance and pattern | src/tagged_urn.rs:2223 |
| test0549 | `test0549_matching_semantics_test7_pattern_has_extra_tag` | TEST0549: Reject match when pattern requires a tag absent from instance | src/tagged_urn.rs:2235 |
| test0550 | `test0550_matching_semantics_test8_empty_pattern_matches_anything` | TEST0550: Match any instance against empty pattern with no constraints | src/tagged_urn.rs:2253 |
| test0551 | `test0551_matching_semantics_test9_cross_dimension_constraints` | TEST0551: Reject match when instance and pattern have non-overlapping tag dimensions | src/tagged_urn.rs:2273 |
| test0552 | `test0552_matching_different_prefixes_error` | TEST0552: Return error for conforms_to, accepts, and is_more_specific_than with different prefixes | src/tagged_urn.rs:2292 |
| test0553 | `test0553_valueless_tag_parsing_single` | TEST0553: Parse single value-less tag as wildcard | src/tagged_urn.rs:2314 |
| test0554 | `test0554_valueless_tag_parsing_multiple` | TEST0554: Parse multiple value-less tags and serialize alphabetically | src/tagged_urn.rs:2324 |
| test0555 | `test0555_valueless_tag_mixed_with_valued` | TEST0555: Parse mix of value-less and valued tags together | src/tagged_urn.rs:2336 |
| test0556 | `test0556_valueless_tag_at_end` | TEST0556: Parse value-less tag at end of URN without trailing semicolon | src/tagged_urn.rs:2349 |
| test0557 | `test0557_valueless_tag_equivalence_to_wildcard` | TEST0557: Verify value-less tag is equivalent to explicit wildcard (key=*) | src/tagged_urn.rs:2359 |
| test0558 | `test0558_valueless_tag_matching` | TEST0558: Match value-less wildcard tag against any specific value | src/tagged_urn.rs:2371 |
| test0559 | `test0559_valueless_tag_in_pattern` | TEST0559: Require value-less tag in pattern to be present in instance | src/tagged_urn.rs:2386 |
| test0560 | `test0560_valueless_tag_specificity` | TEST0560: Score value-less wildcard tags with graded specificity | src/tagged_urn.rs:2406 |
| test0561 | `test0561_valueless_tag_roundtrip` | TEST0561: Round-trip value-less tags through parse and serialize | src/tagged_urn.rs:2419 |
| test0562 | `test0562_valueless_tag_case_normalization` | TEST0562: Normalize value-less tag keys to lowercase | src/tagged_urn.rs:2431 |
| test0563 | `test0563_empty_value_still_error` | TEST0563: Reject empty value with equals sign as distinct from value-less tag | src/tagged_urn.rs:2442 |
| test0564 | `test0564_valueless_tag_directional_accepts` | TEST0564: Verify directional accepts of value-less wildcard tags with specific values | src/tagged_urn.rs:2450 |
| test0565 | `test0565_valueless_numeric_key_still_rejected` | TEST0565: Reject purely numeric keys for value-less tags | src/tagged_urn.rs:2469 |
| test0566 | `test0566_whitespace_in_input_rejected` | TEST0566: Reject leading, trailing, and embedded whitespace in URN input | src/tagged_urn.rs:2477 |
| test0567 | `test0567_unspecified_question_mark_parsing` | TEST0567: Parse question mark as unspecified value and verify serialization. All three input aliases (?x, x?, x=?) parse to the same stored value `"?"` and serialize as the canonical prefix form `?x`. | src/tagged_urn.rs:2522 |
| test0568 | `test0568_must_not_have_exclamation_parsing` | TEST0568: Parse exclamation mark as must-not-have value and verify serialization. All three input aliases (!x, x!, x=!) parse to stored value `"!"` and serialize as canonical `!x`. | src/tagged_urn.rs:2533 |
| test0569 | `test0569_question_mark_pattern_matches_anything` | TEST0569: Match any instance against pattern with unspecified (?) tag value | src/tagged_urn.rs:2542 |
| test0570 | `test0570_question_mark_in_instance` | TEST0570: Match instance with unspecified (?) tag against any pattern constraint | src/tagged_urn.rs:2561 |
| test0571 | `test0571_must_not_have_pattern_requires_absent` | TEST0571: Require tag to be absent when pattern uses must-not-have (!) value | src/tagged_urn.rs:2580 |
| test0572 | `test0572_must_not_have_in_instance` | TEST0572: Reject instance with must-not-have (!) tag against patterns requiring that tag | src/tagged_urn.rs:2597 |
| test0573 | `test0573_full_cross_product_matching` | TEST0573: Verify full cross-product truth table for all instance/pattern value combinations | src/tagged_urn.rs:2616 |
| test0574 | `test0574_mixed_special_values` | TEST0574: Match URN with mixed required, optional, forbidden, and exact tags | src/tagged_urn.rs:2673 |
| test0575 | `test0575_serialization_round_trip_special_values` | TEST0575: Round-trip all special values (?, !, *, exact) through parse and serialize | src/tagged_urn.rs:2696 |
| test0576 | `test0576_bidirectional_accepts_with_special_values` | TEST0576: Check bidirectional accepts between !, *, ?, and specific value tags | src/tagged_urn.rs:2715 |
| test0577 | `test0577_specificity_with_special_values` | TEST0577: Verify graded specificity scores and tuples for special value types under the six-form ladder. | src/tagged_urn.rs:2866 |
| test578 | `test578_equivalent_identical_tags` | TEST578: Equivalent URNs with identical tag sets | src/tagged_urn.rs:2747 |
| test579 | `test579_not_equivalent_when_one_more_specific` | TEST579: Non-equivalent URNs where one is more specific | src/tagged_urn.rs:2756 |
| test580 | `test580_comparable_specialization_chain` | TEST580: Comparable URNs on the same specialization chain | src/tagged_urn.rs:2765 |
| test581 | `test581_incomparable_different_branches` | TEST581: Incomparable URNs in different branches of the lattice | src/tagged_urn.rs:2777 |
| test582 | `test582_equivalent_implies_comparable` | TEST582: Equivalent implies comparable but not vice versa | src/tagged_urn.rs:2789 |
| test583 | `test583_prefix_mismatch_errors` | TEST583: Prefix mismatch returns error for both relations | src/tagged_urn.rs:2805 |
| test584 | `test584_empty_tags_comparable_to_all` | TEST584: Empty tag set is comparable to everything with same prefix | src/tagged_urn.rs:2814 |
| test585 | `test585_string_variants` | TEST585: String variants of is_equivalent and is_comparable | src/tagged_urn.rs:2828 |
| test586 | `test586_special_values` | TEST586: Special values (*, !, ?) with is_equivalent and is_comparable | src/tagged_urn.rs:2838 |
| test587 | `test587_builder_fluent_api` | TEST587: Builder fluent API for tag manipulation | src/tagged_urn.rs:2896 |
| test588 | `test588_builder_custom_tags` | TEST588: Builder with custom tags | src/tagged_urn.rs:2913 |
| test589 | `test589_builder_tag_overrides` | TEST589: Builder tag overrides (last value wins) | src/tagged_urn.rs:2928 |
| test590 | `test590_builder_empty_build` | TEST590: Builder empty build returns error (tags required) | src/tagged_urn.rs:2941 |
| test591 | `test591_builder_single_tag` | TEST591: Builder with single tag | src/tagged_urn.rs:2952 |
| test592 | `test592_builder_complex` | TEST592: Builder with complex multi-tag URN | src/tagged_urn.rs:2966 |
| test593 | `test593_builder_wildcards` | TEST593: Builder with wildcards | src/tagged_urn.rs:2994 |
| test594 | `test594_builder_custom_prefix` | TEST594: Builder with custom prefix | src/tagged_urn.rs:3014 |
| test595 | `test595_builder_matching_with_built_urn` | TEST595: Builder matching with built URN | src/tagged_urn.rs:3026 |
---

*Generated from Rust source tree*
*Total tests: 96*
*Total numbered tests: 96*
*Total unnumbered tests: 0*
*Total numbered tests missing descriptions: 0*
*Total numbering mismatches: 0*
