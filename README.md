# stack_format_string_function_rust


```rust

/// Formats a message with one variable part inserted at {} placeholder.
///
/// ## Project Context
/// Provides simple string formatting for UI messages without heap allocation
/// in the formatting logic itself. Used for status messages, notifications,
/// and other non-critical display text.
///
/// ## Operation
/// Takes a template string with "{}" placeholder and inserts a variable string.
/// Example: ("inserted {} bytes", "42", "fallback") -> "inserted 42 bytes"
/// On any error, returns the fallback string instead.
///
/// ## Safety & Error Handling
/// - No panic: Always returns a valid string (formatted or fallback)
/// - No unwrap: Direct return, no Result to unwrap
/// - Uses 256-byte stack buffer for formatting
/// - Returns fallback if result exceeds buffer size
/// - Returns fallback if template has no {} or invalid format
///
/// ## Parameters
/// - `template`: String with exactly one "{}" placeholder
/// - `insert`: String to insert at the placeholder
/// - `fallback`: Message to return if formatting fails (never empty unless you pass "")
///
/// ## Returns
/// Formatted string on success, fallback string on any error (always valid)
///
/// # example use:
/// let msg = stack_format_it("The cat in the {}", "hat", "");
/// ##  Returns "The cat in the hat" or "" on error
///
fn stack_format_it(template: &str, insert: &str, fallback: &str) -> String {
    // Internal stack buffer for result
    let mut buf = [0u8; 128];

    // Find the "{}" placeholder
    let placeholder = "{}";
    let split_pos = match template.find(placeholder) {
        Some(pos) => pos,
        None => {
            #[cfg(debug_assertions)]
            eprintln!("stack_format: No '{{}}' placeholder found in template");
            return fallback.to_string();
        }
    };

    // Split template into before and after placeholder
    let before = &template[..split_pos];
    let after = &template[split_pos + placeholder.len()..];

    // Calculate total length
    let total_len = match before.len().checked_add(insert.len()) {
        Some(temp) => match temp.checked_add(after.len()) {
            Some(total) => total,
            None => {
                #[cfg(debug_assertions)]
                eprintln!("stack_format: Length overflow");
                return fallback.to_string();
            }
        },
        None => {
            #[cfg(debug_assertions)]
            eprintln!("stack_format: Length overflow");
            return fallback.to_string();
        }
    };

    // Check buffer capacity
    if total_len > buf.len() {
        #[cfg(debug_assertions)]
        eprintln!(
            "stack_format: Result too large (need {}, have {})",
            total_len,
            buf.len()
        );
        return fallback.to_string();
    }

    // Copy parts into buffer: before + insert + after
    let mut pos = 0;

    // Copy "before" part
    buf[pos..pos + before.len()].copy_from_slice(before.as_bytes());
    pos += before.len();

    // Copy insert part
    buf[pos..pos + insert.len()].copy_from_slice(insert.as_bytes());
    pos += insert.len();

    // Copy "after" part
    buf[pos..pos + after.len()].copy_from_slice(after.as_bytes());

    // Validate UTF-8 and return
    match std::str::from_utf8(&buf[..total_len]) {
        Ok(s) => s.to_string(),
        Err(_) => {
            #[cfg(debug_assertions)]
            eprintln!("stack_format: Invalid UTF-8 in result");
            fallback.to_string()
        }
    }
}

```
