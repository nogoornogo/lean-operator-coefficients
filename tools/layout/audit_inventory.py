"""Exact count-message comparison; Lean's unchanged strict audits are authoritative."""


def count_message_matches(before, after, record, old_count, new_count):
    """Allow one recorded final-integer change, preserving every other message."""
    count = record.get('messageCount', 1)
    index = record.get('messageIndex', 0)
    if (type(count) is not int or type(index) is not int or count < 1
            or not 0 <= index < count or len(before) != count or len(after) != count):
        return False
    expected = [list(row) for row in before]
    actual = [list(row) for row in after]
    if not expected[index] or expected[index][-1] != old_count:
        return False
    expected[index][-1] = new_count
    return expected == actual


def inventory_name_allowed(name, label, new_names, new_constants, protected, extension_modules=()):
    """Source extensions cannot hide removed public names or unrelated additions."""
    import re
    if name in protected:
        return False
    if (label == 'added' and new_constants.get(name, {}).get('module') in extension_modules):
        return True
    match = re.search(r'\.(?:_proof_|_simp_|match_)\d+(?:_\d+)*$', name)
    return bool(match and name[:match.start()] in new_names)
