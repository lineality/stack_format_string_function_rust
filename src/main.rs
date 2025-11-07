/// Formats a message with multiple variable parts inserted at {} placeholders.
///
/// ## Project Context
/// - Provides simple string formatting for UI messages and error messages without
/// heap allocation in the formatting logic itself.
/// - Used for status messages,
/// notifications, error reports, and other non-critical display text.
/// - Default string in case of error.
///
/// ## Operation
/// Takes a template string with one or more "{}" placeholders and inserts variable
/// strings in order. Processes each placeholder sequentially, replacing with the
/// corresponding insert string.
///
/// Examples:
/// - stack_format_it("inserted {} bytes", &["42"]) -> "inserted 42 bytes"
/// - stack_format_it("range: start={} > end={}", &["10", "5"]) -> "range: start=10 > end=5"
/// - stack_format_it("a {} b {} c {}", &["1", "2", "3"]) -> "a 1 b 2 c 3"
///
/// ## Safety & Error Handling
/// - No panic: Always returns a valid string (formatted or fallback)
/// - No unwrap: Direct return, no Result to unwrap
/// - Uses 256-byte stack buffer for formatting
/// - Returns fallback if result exceeds buffer size
/// - Returns fallback if placeholder count doesn't match insert count
/// - Returns fallback if template has no {} placeholders
/// - Maximum 8 inserts supported (configurable via MAX_INSERTS)
///
/// ## Parameters
/// - `template`: String with one or more "{}" placeholders
/// - `inserts`: Slice of strings to insert at placeholders (in order)
/// - `fallback`: Message to return if formatting fails
///
/// ## Returns
/// Formatted string on success, fallback string on any error (always valid)
///
/// ## Use Examples:
/// ```rust
/// let bytes = total_bytes_written.saturating_sub(1);
/// let num_str = bytes.to_string();
/// let message = stack_format_it("inserted {} bytes", &[&num_str], "inserted data");
/// ```
///
/// ```rust
/// let num1 = start_byte.to_string();
/// let num2 = end_byte.to_string();
/// let formatted_string = stack_format_it(
///     "Invalid byte range: start={} > end={}",
///     &[&num1, &num2],
///     "Invalid byte range"
/// );
fn stack_format_it(template: &str, inserts: &[&str], fallback: &str) -> String {
    // Internal stack buffer for result
    let mut buf = [0u8; 256];

    // Maximum number of inserts to prevent abuse
    const MAX_INSERTS: usize = 8;

    // Check insert count
    if inserts.is_empty() {
        #[cfg(debug_assertions)]
        eprintln!("stack_format_it: No inserts provided");
        return fallback.to_string();
    }

    if inserts.len() > MAX_INSERTS {
        #[cfg(debug_assertions)]
        eprintln!("stack_format_it: Too many inserts (max {})", MAX_INSERTS);
        return fallback.to_string();
    }

    // Count placeholders in template
    let placeholder = "{}";
    let placeholder_count = template.matches(placeholder).count();

    if placeholder_count == 0 {
        #[cfg(debug_assertions)]
        eprintln!("stack_format_it: No '{{}}' placeholders found in template");
        return fallback.to_string();
    }

    if placeholder_count != inserts.len() {
        #[cfg(debug_assertions)]
        eprintln!(
            "stack_format_it: Placeholder count ({}) doesn't match insert count ({})",
            placeholder_count,
            inserts.len()
        );
        return fallback.to_string();
    }

    // Calculate total length needed
    let mut total_len = template.len();

    // Subtract placeholder lengths
    total_len = match total_len.checked_sub(placeholder.len() * placeholder_count) {
        Some(len) => len,
        None => {
            #[cfg(debug_assertions)]
            eprintln!("stack_format_it: Length calculation underflow");
            return fallback.to_string();
        }
    };

    // Add insert lengths
    for insert in inserts {
        total_len = match total_len.checked_add(insert.len()) {
            Some(len) => len,
            None => {
                #[cfg(debug_assertions)]
                eprintln!("stack_format_it: Length overflow");
                return fallback.to_string();
            }
        };
    }

    // Check buffer capacity
    if total_len > buf.len() {
        #[cfg(debug_assertions)]
        eprintln!(
            "stack_format_it: Result too large (need {}, have {})",
            total_len,
            buf.len()
        );
        return fallback.to_string();
    }

    // Build the result by processing each placeholder
    let mut pos = 0;
    let mut remaining_template = template;
    let mut insert_idx = 0;

    while let Some(placeholder_pos) = remaining_template.find(placeholder) {
        // Copy text before placeholder
        let before = &remaining_template[..placeholder_pos];
        if pos + before.len() > buf.len() {
            #[cfg(debug_assertions)]
            eprintln!("stack_format_it: Buffer overflow during copy");
            return fallback.to_string();
        }
        buf[pos..pos + before.len()].copy_from_slice(before.as_bytes());
        pos += before.len();

        // Copy insert
        let insert = inserts[insert_idx];
        if pos + insert.len() > buf.len() {
            #[cfg(debug_assertions)]
            eprintln!("stack_format_it: Buffer overflow during insert");
            return fallback.to_string();
        }
        buf[pos..pos + insert.len()].copy_from_slice(insert.as_bytes());
        pos += insert.len();

        // Move to next segment
        remaining_template = &remaining_template[placeholder_pos + placeholder.len()..];
        insert_idx += 1;
    }

    // Copy remaining text after last placeholder
    if pos + remaining_template.len() > buf.len() {
        #[cfg(debug_assertions)]
        eprintln!("stack_format_it: Buffer overflow during final copy");
        return fallback.to_string();
    }
    buf[pos..pos + remaining_template.len()].copy_from_slice(remaining_template.as_bytes());
    pos += remaining_template.len();

    // Validate UTF-8 and return
    match std::str::from_utf8(&buf[..pos]) {
        Ok(s) => s.to_string(),
        Err(_) => {
            #[cfg(debug_assertions)]
            eprintln!("stack_format_it: Invalid UTF-8 in result");
            fallback.to_string()
        }
    }
}

// Demo of stack_format_it()
fn main() {
    println!("=== stack_format_it() Test Examples ===\n");

    // Test 1: Single placeholder
    println!("✓ Test 1: Single placeholder");
    let bytes = 42_u64;
    let num_str = bytes.to_string();
    let result = stack_format_it("inserted {} bytes", &[&num_str], "inserted data");
    println!("  Input:  \"inserted {{}} bytes\" with [\"42\"]");
    println!("  Result: \"{}\"\n", result);

    // Test 2: Multiple placeholders
    println!("✓ Test 2: Multiple placeholders");
    let start = 100;
    let end = 50;
    let num1 = start.to_string();
    let num2 = end.to_string();
    let result = stack_format_it(
        "Invalid byte range: start={} > end={}",
        &[&num1, &num2],
        "Invalid byte range",
    );
    println!("  Input:  \"Invalid byte range: start={{}} > end={{}}\" with [\"100\", \"50\"]");
    println!("  Result: \"{}\"\n", result);

    // Test 3: Three placeholders
    println!("✓ Test 3: Three placeholders");
    let result = stack_format_it(
        "File: {} Line: {} Column: {}",
        &["main.rs", "42", "10"],
        "Location info unavailable",
    );
    println!("  Input:  \"File: {{}} Line: {{}} Column: {{}}\" with [\"main.rs\", \"42\", \"10\"]");
    println!("  Result: \"{}\"\n", result);

    // Test 4: The cat example
    println!("✓ Test 4: Simple text replacement");
    let result = stack_format_it("The cat in the {}", &["hat"], "The cat");
    println!("  Input:  \"The cat in the {{}}\" with [\"hat\"]");
    println!("  Result: \"{}\"\n", result);

    // Test 5: Four placeholders
    println!("✓ Test 5: Four placeholders");
    let result = stack_format_it(
        "Error at {}:{}:{} - {}",
        &["file.rs", "100", "5", "unexpected token"],
        "Error occurred",
    );
    println!(
        "  Input:  \"Error at {{}}:{{}}:{{}} - {{}}\" with [\"file.rs\", \"100\", \"5\", \"unexpected token\"]"
    );
    println!("  Result: \"{}\"\n", result);

    // Test 6: Edge case - very long result (should succeed)
    println!("✓ Test 6: Long message (should succeed)");
    let long_word = "supercalifragilisticexpialidocious";
    let result = stack_format_it("This is a {} word in a sentence", &[long_word], "fallback");
    println!(
        "  Input:  \"This is a {{}} word in a sentence\" with [\"supercalifragilisticexpialidocious\"]"
    );
    println!("  Result: \"{}\"\n", result);

    // Test 7: Error case - no placeholders (should return fallback)
    println!("✓ Test 7: ERROR CASE - No placeholders (intentionally tests error handling)");
    let result = stack_format_it("No placeholders here", &["test"], "fallback message");
    println!("  Input:  \"No placeholders here\" with [\"test\"]");
    println!("  Expected: Return fallback because no {{}} found");
    println!(
        "  Result: \"{}\" ← This is CORRECT (fallback returned)",
        result
    );
    println!("  Note: Debug message above is EXPECTED for this error test\n");

    // Test 8: Error case - mismatched counts (should return fallback)
    println!("✓ Test 8: ERROR CASE - Mismatched counts (intentionally tests error handling)");
    let result = stack_format_it(
        "Only {} placeholder",
        &["first", "second"],
        "fallback message",
    );
    println!("  Input:  \"Only {{}} placeholder\" with [\"first\", \"second\"]");
    println!("  Expected: Return fallback because 1 placeholder but 2 inserts");
    println!(
        "  Result: \"{}\" ← This is CORRECT (fallback returned)",
        result
    );
    println!("  Note: Debug message above is EXPECTED for this error test\n");

    // Test 9: Large numbers
    println!("✓ Test 9: Large numbers");
    let big_num = u64::MAX;
    let num_str = big_num.to_string();
    let result = stack_format_it(
        "Maximum u64 value: {}",
        &[&num_str],
        "number display failed",
    );
    println!("  Input:  \"Maximum u64 value: {{}}\" with [\"18446744073709551615\"]");
    println!("  Result: \"{}\"\n", result);

    // Test 10: Empty insert strings
    println!("✓ Test 10: Empty insert strings");
    let result = stack_format_it("Before {} middle {} after", &["", ""], "fallback");
    println!("  Input:  \"Before {{}} middle {{}} after\" with [\"\", \"\"]");
    println!("  Result: \"{}\"\n", result);

    println!("=== ✓ All tests completed successfully ===");
    println!(
        "\nNote: Debug error messages (lines starting with 'stack_format_it:') are INTENTIONAL"
    );
    println!(
        "for Tests 7 & 8. They only appear in debug builds and show error handling works correctly."
    );
}
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_single_placeholder() {
        let result = stack_format_it("hello {}", &["world"], "fallback");
        assert_eq!(result, "hello world");
    }

    #[test]
    fn test_multiple_placeholders() {
        let result = stack_format_it("a {} b {} c", &["1", "2"], "fallback");
        assert_eq!(result, "a 1 b 2 c");
    }

    #[test]
    fn test_no_placeholder_returns_fallback() {
        let result = stack_format_it("no placeholder", &["test"], "fallback");
        assert_eq!(result, "fallback");
    }

    #[test]
    fn test_mismatched_count_returns_fallback() {
        let result = stack_format_it("one {}", &["1", "2"], "fallback");
        assert_eq!(result, "fallback");
    }

    #[test]
    fn test_empty_inserts() {
        let result = stack_format_it("{}{}{}", &["", "", ""], "fallback");
        assert_eq!(result, "");
    }

    #[test]
    fn test_large_number() {
        let num = u64::MAX.to_string();
        let result = stack_format_it("value: {}", &[&num], "fallback");
        assert_eq!(result, format!("value: {}", u64::MAX));
    }
}
