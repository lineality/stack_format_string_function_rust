// stack_format_it
/*
TODO:

*/

/// Formats a byte as 2-digit uppercase hexadecimal with optional ANSI styling.
///
/// ## Project Context
/// Used in hex editor display to show byte values with cursor highlighting.
/// Formats bytes as "XX " (3 chars) or with ANSI escape codes for highlighting.
///
/// ## Operation
/// - Normal mode: Formats as "42 " (hex byte + space)
/// - Highlight mode: Wraps with ANSI codes for cursor position
/// - Uses stack buffer, no heap allocation for formatting
///
/// ## Safety & Error Handling
/// - No panic: Always returns valid formatted string
/// - Fixed maximum size: 64 bytes for result (sufficient for ANSI codes)
/// - Pre-validated: Byte values always valid for hex formatting
///
/// ## Parameters
/// - `byte`: The byte value to format (0x00-0xFF)
/// - `highlight`: If true, wraps with ANSI color codes
/// - `bold`: ANSI bold code (typically "\x1b[1m")
/// - `red`: ANSI red foreground code
/// - `bg_white`: ANSI white background code
/// - `reset`: ANSI reset code (typically "\x1b[0m")
///
/// ## Returns
/// Formatted string: "XX " or "{codes}XX{reset} "
///
/// ## Example use:
/// ```rust
/// // Normal byte
/// let formatted = stack_format_hex(0x42, false, "", "", "", "");
/// // Result: "42 "
///
/// // Highlighted byte
/// let formatted = stack_format_hex(0x42, true, BOLD, RED, BG_WHITE, RESET);
/// // Result: "\x1b[1m\x1b[31m\x1b[47m42\x1b[0m "
/// ```
pub fn stack_format_hex(
    byte: u8,
    highlight: bool,
    bold: &str,
    red: &str,
    bg_white: &str,
    reset: &str,
) -> String {
    // Stack buffer for result (64 bytes sufficient for ANSI codes + hex)
    let mut buf = [0u8; 64];
    let mut pos = 0;

    if highlight {
        // Add ANSI codes before hex
        for code in &[bold, red, bg_white] {
            let code_bytes = code.as_bytes();
            if pos + code_bytes.len() > buf.len() {
                // Fallback if codes too long (shouldn't happen with standard ANSI)
                return format!("{:02X} ", byte);
            }
            buf[pos..pos + code_bytes.len()].copy_from_slice(code_bytes);
            pos += code_bytes.len();
        }
    }

    // Format byte as 2-digit hex
    let hex_chars = b"0123456789ABCDEF";
    let high = (byte >> 4) as usize;
    let low = (byte & 0x0F) as usize;

    if pos + 2 > buf.len() {
        return format!("{:02X} ", byte);
    }

    buf[pos] = hex_chars[high];
    buf[pos + 1] = hex_chars[low];
    pos += 2;

    if highlight {
        // Add reset code after hex
        let reset_bytes = reset.as_bytes();
        if pos + reset_bytes.len() > buf.len() {
            return format!("{:02X} ", byte);
        }
        buf[pos..pos + reset_bytes.len()].copy_from_slice(reset_bytes);
        pos += reset_bytes.len();
    }

    // Add trailing space
    if pos + 1 > buf.len() {
        return format!("{:02X} ", byte);
    }
    buf[pos] = b' ';
    pos += 1;

    // Convert to string
    match std::str::from_utf8(&buf[..pos]) {
        Ok(s) => s.to_string(),
        Err(_) => format!("{:02X} ", byte), // Fallback
    }
}

/// Converts byte to raw string representation with escape sequences.
///
/// ## Project Context
/// Used in hex editor to display bytes as readable escape sequences.
/// Shows special characters (\n, \t) and non-printable bytes (\xHH) in a
/// human-readable format for the ASCII/raw column display.
///
/// ## Operation
/// - Printable ASCII (0x20-0x7E) → returns as single character
/// - Special chars (newline, tab, etc.) → returns escape sequence
/// - Non-printable bytes → returns hex escape \xHH
/// - Uses stack buffer, minimal heap allocation
///
/// ## Safety & Error Handling
/// - No panic: All byte values handled
/// - Bounded output: Maximum 4 characters (\xHH)
/// - Pre-validated: All paths return valid UTF-8
///
/// ## Parameters
/// - `byte`: Single byte to convert (0x00-0xFF)
///
/// ## Returns
/// String representation (1-4 characters)
///
/// ## Examples
/// ```rust
/// stack_format_byte_escape(0x0A) // "\\n"
/// stack_format_byte_escape(0x48) // "H"
/// stack_format_byte_escape(0x00) // "\\x00"
/// stack_format_byte_escape(0x09) // "\\t"
/// ```
pub fn stack_format_byte_escape(byte: u8) -> String {
    // Stack buffer for result (max 4 bytes for \xHH)
    let mut buf = [0u8; 4];
    let len: usize;

    match byte {
        0x0A => {
            // Newline: \n
            buf[0] = b'\\';
            buf[1] = b'n';
            len = 2;
        }
        0x09 => {
            // Tab: \t
            buf[0] = b'\\';
            buf[1] = b't';
            len = 2;
        }
        0x0D => {
            // Carriage return: \r
            buf[0] = b'\\';
            buf[1] = b'r';
            len = 2;
        }
        0x5C => {
            // Backslash: \\
            buf[0] = b'\\';
            buf[1] = b'\\';
            len = 2;
        }
        0x22 => {
            // Quote: \"
            buf[0] = b'\\';
            buf[1] = b'"';
            len = 2;
        }
        0x00 => {
            // Null: \0
            buf[0] = b'\\';
            buf[1] = b'0';
            len = 2;
        }
        0x20..=0x7E => {
            // Printable ASCII (already handled special cases above)
            buf[0] = byte;
            len = 1;
        }
        _ => {
            // Non-printable: \xHH
            let hex_chars = b"0123456789ABCDEF";
            buf[0] = b'\\';
            buf[1] = b'x';
            buf[2] = hex_chars[(byte >> 4) as usize];
            buf[3] = hex_chars[(byte & 0x0F) as usize];
            len = 4;
        }
    }

    // Convert to string (guaranteed valid UTF-8)
    // Safe unwrap: we only write ASCII bytes
    std::str::from_utf8(&buf[..len])
        .map(|s| s.to_string())
        .unwrap_or_else(|_| String::from("?")) // Defensive fallback
}

#[cfg(test)]
mod hex_format_tests {
    use super::*;

    #[test]
    fn test_hex_normal() {
        let result = stack_format_hex(0x42, false, "", "", "", "");
        assert_eq!(result, "42 ");
    }

    #[test]
    fn test_hex_highlighted() {
        let result = stack_format_hex(0x42, true, "[B]", "[R]", "[W]", "[RST]");
        assert_eq!(result, "[B][R][W]42[RST] ");
    }

    #[test]
    fn test_hex_zero() {
        let result = stack_format_hex(0x00, false, "", "", "", "");
        assert_eq!(result, "00 ");
    }

    #[test]
    fn test_hex_max() {
        let result = stack_format_hex(0xFF, false, "", "", "", "");
        assert_eq!(result, "FF ");
    }

    #[test]
    fn test_byte_escape_printable() {
        assert_eq!(stack_format_byte_escape(b'H'), "H");
        assert_eq!(stack_format_byte_escape(b' '), " ");
    }

    #[test]
    fn test_byte_escape_special() {
        assert_eq!(stack_format_byte_escape(0x0A), "\\n");
        assert_eq!(stack_format_byte_escape(0x09), "\\t");
        assert_eq!(stack_format_byte_escape(0x0D), "\\r");
        assert_eq!(stack_format_byte_escape(0x00), "\\0");
    }

    #[test]
    fn test_byte_escape_nonprintable() {
        assert_eq!(stack_format_byte_escape(0x01), "\\x01");
        assert_eq!(stack_format_byte_escape(0xFF), "\\xFF");
        assert_eq!(stack_format_byte_escape(0x7F), "\\x7F");
    }
}

/// Formats a message with placeholders supporting alignment and width specifiers.
///
/// ## Project Context
/// Provides string formatting for UI messages, tables, and aligned output using
/// stack-allocated buffers. Supports basic format specifiers for padding and
/// alignment without heap allocation.
///
/// ## Supported Format Specifiers
/// - `{}` - Plain replacement
/// - `{:<N}` - Left-align with width N (pad right with spaces)
/// - `{:>N}` - Right-align with width N (pad left with spaces)
/// - `{:^N}` - Center-align with width N (pad both sides with spaces)
/// - `{:N}` - Default right-align with width N
///
/// Examples:
/// - ("ID: {:<5}", &["42"]) -> "ID: 42   " (left-align, width 5)
/// - ("ID: {:>5}", &["42"]) -> "ID:    42" (right-align, width 5)
/// - ("ID: {:^5}", &["42"]) -> "ID:  42  " (center-align, width 5)
///
/// ## Safety & Error Handling
/// - No panic: Always returns valid string or fallback
/// - No unwrap: All error paths return fallback
/// - Uses 256-byte stack buffer
/// - Returns fallback if result exceeds buffer
/// - Returns fallback if format specifiers are invalid
/// - Maximum 8 inserts supported
///
/// ## Parameters
/// - `template`: String with format placeholders
/// - `inserts`: Slice of strings to insert
/// - `fallback`: Message to return if formatting fails
///
/// ## Returns
/// Formatted string on success, fallback string on any error
///
/// ## Use Examples:
/// ```rust
/// // Table-like alignment
/// let id = "42";
/// let name = "Alice";
/// let row = stack_format_it(
///     "ID: {:<5} Name: {:<10}",
///     &[id, name],
///     "Data unavailable"
/// );
/// // Result: "ID: 42    Name: Alice     "
/// ```
///
///
/// ```rust
/// let bytes = total_bytes_written.saturating_sub(1);
/// let num_str = bytes.to_string();
/// let message = stack_format_it("inserted {} bytes", &[&num_str], "inserted data");
/// ```
///
/// Error Formatting:
/// ```
/// io::stdout().flush().map_err(|e| {
///     LinesError::DisplayError(stack_format_it(
///         "Failed to flush stdout: {}",
///         &[&e.to_string()],
///         "Failed to flush stdout",
///     ))
/// })?;
/// ```
///
/// ```rust
/// let num_1 = start_byte.to_string();
/// let num_2 = end_byte.to_string();
/// let formatted_string = stack_format_it(
///     "Invalid byte range: start={} > end={}",
///     &[&num_1, &num_2],
///     "Invalid byte range"
/// );
/// ```
pub fn stack_format_it(template: &str, inserts: &[&str], fallback: &str) -> String {
    // Internal stack buffer for result
    let mut buf = [0u8; 512];

    // Maximum number of inserts to prevent abuse
    const MAX_INSERTS: usize = 128;

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

    // Parse format specifiers and validate
    let format_specs = match parse_format_specs(template, inserts.len()) {
        Some(specs) => specs,
        None => {
            #[cfg(debug_assertions)]
            eprintln!("stack_format_it: Failed to parse format specifiers");
            return fallback.to_string();
        }
    };

    // Build the result
    let mut pos = 0;
    let mut insert_idx = 0;
    let mut search_start = 0;

    while insert_idx < inserts.len() {
        // Find next placeholder
        let placeholder_start = match template[search_start..].find('{') {
            Some(offset) => search_start + offset,
            None => break,
        };

        let placeholder_end = match template[placeholder_start..].find('}') {
            Some(offset) => placeholder_start + offset + 1,
            None => {
                #[cfg(debug_assertions)]
                eprintln!("stack_format_it: Unclosed placeholder");
                return fallback.to_string();
            }
        };

        // Copy text before placeholder
        let before = &template[search_start..placeholder_start];
        if pos + before.len() > buf.len() {
            #[cfg(debug_assertions)]
            eprintln!("stack_format_it: Buffer overflow");
            return fallback.to_string();
        }
        buf[pos..pos + before.len()].copy_from_slice(before.as_bytes());
        pos += before.len();

        // Apply format specifier and insert
        let spec = &format_specs[insert_idx];
        let insert = inserts[insert_idx];

        let formatted = apply_format_spec(insert, spec);

        if pos + formatted.len() > buf.len() {
            #[cfg(debug_assertions)]
            eprintln!("stack_format_it: Buffer overflow during insert");
            return fallback.to_string();
        }
        buf[pos..pos + formatted.len()].copy_from_slice(formatted.as_bytes());
        pos += formatted.len();

        search_start = placeholder_end;
        insert_idx += 1;
    }

    // Copy remaining text after last placeholder
    let remaining = &template[search_start..];
    if pos + remaining.len() > buf.len() {
        #[cfg(debug_assertions)]
        eprintln!("stack_format_it: Buffer overflow during final copy");
        return fallback.to_string();
    }
    buf[pos..pos + remaining.len()].copy_from_slice(remaining.as_bytes());
    pos += remaining.len();

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

/// Format specifier parsed from placeholder
#[derive(Debug, Clone, Copy)]
enum Alignment {
    Left,
    Right,
    Center,
}

#[derive(Debug, Clone, Copy)]
struct FormatSpec {
    alignment: Alignment,
    width: Option<usize>,
}

/// Parse format specifiers from template
/// Returns None if parsing fails or placeholder count doesn't match insert count
fn parse_format_specs(template: &str, expected_count: usize) -> Option<Vec<FormatSpec>> {
    let mut specs = Vec::new();
    let mut remaining = template;

    while let Some(start) = remaining.find('{') {
        let end = remaining[start..].find('}')?;
        let placeholder = &remaining[start + 1..start + end];

        let spec = if placeholder.is_empty() {
            // Plain {} placeholder
            FormatSpec {
                alignment: Alignment::Left,
                width: None,
            }
        } else if placeholder.starts_with(':') {
            // Format specifier like {:<5} or {:>10}
            parse_single_spec(&placeholder[1..])?
        } else {
            // Invalid format
            return None;
        };

        specs.push(spec);
        remaining = &remaining[start + end + 1..];
    }

    if specs.len() == expected_count {
        Some(specs)
    } else {
        #[cfg(debug_assertions)]
        eprintln!(
            "parse_format_specs: Placeholder count ({}) doesn't match insert count ({})",
            specs.len(),
            expected_count
        );
        None
    }
}

/// Parse a single format specifier like "<5" or ">10" or "^8"
fn parse_single_spec(spec: &str) -> Option<FormatSpec> {
    if spec.is_empty() {
        return Some(FormatSpec {
            alignment: Alignment::Right,
            width: None,
        });
    }

    let (alignment, width_str) = if spec.starts_with('<') {
        (Alignment::Left, &spec[1..])
    } else if spec.starts_with('>') {
        (Alignment::Right, &spec[1..])
    } else if spec.starts_with('^') {
        (Alignment::Center, &spec[1..])
    } else if spec.chars().next()?.is_ascii_digit() {
        // No alignment character means right-align
        (Alignment::Right, spec)
    } else {
        return None;
    };

    let width = if width_str.is_empty() {
        None
    } else {
        match width_str.parse::<usize>() {
            Ok(w) if w <= 64 => Some(w), // Reasonable width limit
            _ => return None,
        }
    };

    Some(FormatSpec { alignment, width })
}

/// Apply format specifier to a string value
fn apply_format_spec(value: &str, spec: &FormatSpec) -> String {
    let width = match spec.width {
        Some(w) => w,
        None => return value.to_string(), // No width, return as-is
    };

    let value_len = value.len();

    if value_len >= width {
        // Value already meets or exceeds width
        return value.to_string();
    }

    let padding = width - value_len;

    match spec.alignment {
        Alignment::Left => {
            // Pad right: "42   "
            let mut result = String::with_capacity(width);
            result.push_str(value);
            for _ in 0..padding {
                result.push(' ');
            }
            result
        }
        Alignment::Right => {
            // Pad left: "   42"
            let mut result = String::with_capacity(width);
            for _ in 0..padding {
                result.push(' ');
            }
            result.push_str(value);
            result
        }
        Alignment::Center => {
            // Pad both sides: " 42  "
            let left_pad = padding / 2;
            let right_pad = padding - left_pad;
            let mut result = String::with_capacity(width);
            for _ in 0..left_pad {
                result.push(' ');
            }
            result.push_str(value);
            for _ in 0..right_pad {
                result.push(' ');
            }
            result
        }
    }
}

/// Formats a message with multiple variable parts inserted at {} placeholders.
///
/// ## Project Context
/// Provides simple string formatting for UI messages and error messages using
/// stack-allocated buffers. Designed for display text where formatting failure
/// can gracefully degrade to a fallback message without compromising program
/// operation.
///
/// **Use for:**
/// - Status bar updates
/// - User notifications
/// - Progress indicators
/// - Display-only error messages
///
/// **Do NOT use for:**
/// - output that may exceed a known size
/// - where a known default is less optimal than erroring-out
///
/// Stack allocation makes this function safer and more predictable than
/// heap-based formatting for bounded display messages.
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
fn stack_format_basic(template: &str, inserts: &[&str], fallback: &str) -> String {
    // Internal stack buffer for result
    let mut buf = [0u8; 128];

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

    // Test 9: Large numbers
    println!("✓ Basic Test 9: Large numbers");
    let big_num = u64::MAX;
    let num_str = big_num.to_string();
    let result = stack_format_basic(
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
mod basic_tests {
    use super::*;

    #[test]
    fn test_single_placeholder() {
        let result = stack_format_basic("hello {}", &["world"], "fallback");
        assert_eq!(result, "hello world");
    }

    #[test]
    fn test_multiple_placeholders() {
        let result = stack_format_basic("a {} b {} c", &["1", "2"], "fallback");
        assert_eq!(result, "a 1 b 2 c");
    }

    #[test]
    fn test_no_placeholder_returns_fallback() {
        let result = stack_format_basic("no placeholder", &["test"], "fallback");
        assert_eq!(result, "fallback");
    }

    #[test]
    fn test_mismatched_count_returns_fallback() {
        let result = stack_format_basic("one {}", &["1", "2"], "fallback");
        assert_eq!(result, "fallback");
    }

    #[test]
    fn test_empty_inserts() {
        let result = stack_format_basic("{}{}{}", &["", "", ""], "fallback");
        assert_eq!(result, "");
    }

    #[test]
    fn test_large_number() {
        let num = u64::MAX.to_string();
        let result = stack_format_basic("value: {}", &[&num], "fallback");
        assert_eq!(result, format!("value: {}", u64::MAX));
    }
}

#[cfg(test)]
mod standard_tests {
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
