#!/usr/bin/env python3
"""Negative controls for exact multi-message compiler-helper reconciliation."""
import unittest
from audit_inventory import count_message_matches, inventory_name_allowed


class InventoryTests(unittest.TestCase):
    def test_original_single_message(self):
        self.assertTrue(count_message_matches([(3, 305)], [(3, 285)], {}, 305, 285))
        self.assertFalse(count_message_matches([(3, 305)], [(4, 285)], {}, 305, 285))

    def test_one_selected_message(self):
        before = [(n,) for n in range(16)]
        before[4] = (305,)
        after = before.copy()
        after[4] = (285,)
        record = dict(messageCount=16, messageIndex=4)
        self.assertTrue(count_message_matches(before, after, record, 305, 285))
        after[5] = (6,)
        self.assertFalse(count_message_matches(before, after, record, 305, 285))

    def test_added_message_or_wrong_position(self):
        record = dict(messageCount=2, messageIndex=1)
        self.assertFalse(count_message_matches([(1,), (305,)], [(1,), (285,), (9,)],
                                              record, 305, 285))
        self.assertFalse(count_message_matches([(305,), (1,)], [(285,), (1,)],
                                              record, 305, 285))

    def test_invalid_record(self):
        for record in [dict(messageIndex=-1), dict(messageCount=0),
                       dict(messageIndex=True), dict(messageCount='1')]:
            self.assertFalse(count_message_matches([(305,)], [(285,)], record, 305, 285))


    def test_extension_cannot_hide_removed_source_or_unrelated_additions(self):
        new = {'N.retained', 'N.newLemma', 'N.retained._proof_1'}
        constants = {'N.newLemma': {'module': 'Reviewed.New'}}
        self.assertTrue(inventory_name_allowed('N.newLemma','added',new,constants,set(),{'Reviewed.New'}))
        self.assertFalse(inventory_name_allowed('N.newLemma','added',new,constants,set(),{'Unrelated.New'}))
        self.assertFalse(inventory_name_allowed('N.oldLemma','removed',new,constants,set(),{'Reviewed.New'}))
        self.assertFalse(inventory_name_allowed('N.newLemma','added',new,constants,{'N.newLemma'},{'Reviewed.New'}))
        self.assertTrue(inventory_name_allowed('N.retained._proof_1','removed',new,constants,set()))
        self.assertFalse(inventory_name_allowed('N.missing._proof_1','removed',new,constants,set()))


if __name__ == '__main__':
    unittest.main()
