#include <r_anal.h>
#include "minunit.h"

static bool check_invariants(RAnal *anal) {
	RBIter iter;
	RAnalBlock *block;
	ut64 last_start = UT64_MAX;
	r_rbtree_foreach (anal->bb_tree, iter, block, RAnalBlock, _rb) {
		if (last_start != UT64_MAX) {
			mu_assert ("corrupted binary tree", block->addr >= last_start);
			mu_assert_neq (block->addr, last_start, "double blocks");
		}
		last_start = block->addr;

		mu_assert ("block->ref < 1, but it is still in the tree", block->ref >= 1);
		mu_assert ("block->ref < r_list_length (block->fcns)", block->ref >= r_list_length (block->fcns));

		RListIter *fcniter;
		RAnalFunction *fcn;
		r_list_foreach (block->fcns, fcniter, fcn) {
			RListIter *fcniter2;
			RAnalFunction *fcn2;
			for (fcniter2 = fcniter->n; fcniter2 && (fcn2 = fcniter2->data, 1); fcniter2 = fcniter2->n) {
				mu_assert_ptrneq (fcn, fcn2, "duplicate function in basic block");
			}
			mu_assert ("block references function, but function does not reference block", r_list_contains (fcn->bbs, block));
		}
	}

	RListIter *fcniter;
	RAnalFunction *fcn;
	r_list_foreach (anal->fcns, fcniter, fcn) {
		RListIter *blockiter;
		ut64 min = UT64_MAX;
		ut64 max = UT64_MIN;
		ut64 realsz = 0;
		r_list_foreach (fcn->bbs, blockiter, block) {
			RListIter *blockiter2;
			RAnalBlock *block2;
			if (block->addr < min) {
				min = block->addr;
			}
			if (block->addr + block->size > max) {
				max = block->addr + block->size;
			}
			realsz += block->size;
			for (blockiter2 = blockiter->n; blockiter2 && (block2 = blockiter2->data, 1); blockiter2 = blockiter2->n) {
				mu_assert_ptrneq (block, block2, "duplicate basic block in function");
			}
			mu_assert ("function references block, but block does not reference function", r_list_contains (block->fcns, fcn));
		}

		if (fcn->meta._min != UT64_MAX) {
			mu_assert_eq (fcn->meta._min, min, "function min wrong");
			mu_assert_eq (fcn->meta._max, max, "function max wrong");
		}

		mu_assert_eq (r_anal_function_realsize (fcn), realsz, "realsize wrong");
	}
	return true;
}

static bool check_leaks(RAnal *anal) {
	RBIter iter;
	RAnalBlock *block;
	r_rbtree_foreach (anal->bb_tree, iter, block, RAnalBlock, _rb) {
		if (block->ref != r_list_length (block->fcns))  {
			mu_assert ("leaked basic block", false);
		}
	}
	return true;
}

static size_t blocks_count(RAnal *anal) {
	size_t count = 0;
	RBIter iter;
	RAnalBlock *block;
	r_rbtree_foreach(anal->bb_tree, iter, block, RAnalBlock, _rb) {
		count++;
	}
	return count;
}


#define assert_invariants(anal) do { if (!check_invariants (anal)) { return false; } } while (0)
#define assert_leaks(anal) do { if (!check_leaks (anal)) { return false; } } while (0)

bool test_r_anal_block_create() {
	RAnal *anal = r_anal_new ();
	assert_invariants (anal);

	mu_assert_eq (blocks_count (anal), 0, "initial count");

	RAnalBlock *block = r_anal_create_block (anal, 0x1337, 42);
	assert_invariants (anal);
	mu_assert ("created block", block);
	mu_assert_eq (block->addr, 0x1337, "created addr");
	mu_assert_eq (block->size, 42, "created size");
	mu_assert_eq (block->ref, 1, "created initial ref");
	mu_assert_eq (blocks_count (anal), 1, "count after create");

	RAnalBlock *block2 = r_anal_create_block (anal, 0x133f, 100);
	assert_invariants (anal);
	mu_assert ("created block (overlap)", block2);
	mu_assert_eq (block2->addr, 0x133f, "created addr");
	mu_assert_eq (block2->size, 100, "created size");
	mu_assert_eq (block2->ref, 1, "created initial ref");
	mu_assert_eq (blocks_count (anal), 2, "count after create");

	RAnalBlock *block3 = r_anal_create_block (anal, 0x1337, 5);
	assert_invariants (anal);
	mu_assert ("no double create on same start", !block3);
	mu_assert_eq (blocks_count (anal), 2, "count after failed create");

	r_anal_block_unref (block);
	r_anal_block_unref (block2);

	assert_leaks (anal);
	r_anal_free (anal);
	mu_end;
}

bool test_r_anal_block_contains() {
	RAnalBlock dummy = { 0 };
	dummy.addr = 0x1337;
	dummy.size = 42;
	mu_assert ("contains before", !r_anal_block_contains (&dummy, 100));
	mu_assert ("contains start", r_anal_block_contains (&dummy, 0x1337));
	mu_assert ("contains inside", r_anal_block_contains (&dummy, 0x1339));
	mu_assert ("contains last", r_anal_block_contains (&dummy, 0x1337 + 42 - 1));
	mu_assert ("contains after", !r_anal_block_contains (&dummy, 0x1337 + 42));
	mu_end;
}

bool test_r_anal_block_split() {
	RAnal *anal = r_anal_new ();
	assert_invariants (anal);

	RAnalBlock *block = r_anal_create_block (anal, 0x1337, 42);
	assert_invariants (anal);
	mu_assert_eq (blocks_count (anal), 1, "count after create");
	block->jump = 0xdeadbeef;
	block->fail = 0xc0ffee;
	block->ninstr = 5;
	r_anal_bb_set_offset (block, 0, 0);
	r_anal_bb_set_offset (block, 1, 1);
	r_anal_bb_set_offset (block, 2, 2);
	r_anal_bb_set_offset (block, 3, 4);
	r_anal_bb_set_offset (block, 4, 30);

	RAnalBlock *second = r_anal_block_split (block, 0x1337);
	assert_invariants (anal);
	mu_assert_ptreq (second, block, "nop split on first addr");
	mu_assert_eq (blocks_count (anal), 1, "count after nop split");
	mu_assert_eq (block->ref, 2, "ref after nop split");
	r_anal_block_unref (block);

	second = r_anal_block_split (block, 0x1339);
	assert_invariants (anal);
	mu_assert_ptrneq (second, block, "non-nop split");
	mu_assert_eq (blocks_count (anal), 2, "count after non-nop split");

	mu_assert_eq (block->addr, 0x1337, "first addr after split");
	mu_assert_eq (block->size, 2, "first size after split");
	mu_assert_eq (second->addr, 0x1339, "first addr after split");
	mu_assert_eq (second->size, 40, "first size after split");

	mu_assert_eq (block->jump, second->addr, "first jump");
	mu_assert_eq (block->fail, UT64_MAX, "first fail");
	mu_assert_eq (second->jump, 0xdeadbeef, "second jump");
	mu_assert_eq (second->fail, 0xc0ffee, "second fail");

	mu_assert_eq (block->ninstr, 2, "first ninstr after split");
	mu_assert_eq (r_anal_bb_offset_inst (block, 0), 0, "first op_pos[0]");
	mu_assert_eq (r_anal_bb_offset_inst (block, 1), 1, "first op_pos[1]");

	mu_assert_eq (second->ninstr, 3, "second ninstr after split");
	mu_assert_eq (r_anal_bb_offset_inst (second, 0), 0, "second op_pos[0]");
	mu_assert_eq (r_anal_bb_offset_inst (second, 1), 2, "second op_pos[1]");
	mu_assert_eq (r_anal_bb_offset_inst (second, 2), 28, "second op_pos[2]");

	r_anal_block_unref (block);
	r_anal_block_unref (second);

	assert_leaks (anal);
	r_anal_free (anal);
	mu_end;
}

bool test_r_anal_block_split_in_function() {
	RAnal *anal = r_anal_new ();
	assert_invariants (anal);

	RAnalFunction *fcn = r_anal_create_function (anal, "bbowner", 0x1337, 0, NULL);
	assert_invariants (anal);

	RAnalBlock *block = r_anal_create_block (anal, 0x1337, 42);
	assert_invariants (anal);
	mu_assert_eq (blocks_count (anal), 1, "count after create");
	r_anal_function_add_block (fcn, block);
	assert_invariants (anal);
	mu_assert_eq (block->ref, 2, "block refs after adding to function");

	RAnalBlock *second = r_anal_block_split (block, 0x1339);
	assert_invariants (anal);
	mu_assert_ptrneq (second, block, "non-nop split");
	mu_assert_eq (blocks_count (anal), 2, "count after non-nop split");
	mu_assert_eq (block->ref, 2, "first block refs after adding to function");
	mu_assert_eq (second->ref, 2, "second block refs after adding to function");

	mu_assert ("function has first block after split", r_list_contains (fcn->bbs, block));
	mu_assert ("function has second block after split", r_list_contains (fcn->bbs, second));
	mu_assert ("second block is in function after split", r_list_contains (block->fcns, fcn));
	mu_assert ("second block is in function after split", r_list_contains (second->fcns, fcn));

	r_anal_block_unref (block);
	r_anal_block_unref (second);

	assert_leaks (anal);
	r_anal_free (anal);
	mu_end;
}

bool test_r_anal_block_merge() {
	RAnal *anal = r_anal_new ();
	assert_invariants (anal);

	RAnalBlock *first = r_anal_create_block (anal, 0x1337, 42);
	RAnalBlock *second = r_anal_create_block (anal, 0x1337 + 42, 624);
	assert_invariants (anal);
	mu_assert_eq (blocks_count (anal), 2, "count after create");
	second->jump = 0xdeadbeef;
	second->fail = 0xc0ffee;

	first->ninstr = 3;
	r_anal_bb_set_offset (first, 0, 0);
	r_anal_bb_set_offset (first, 1, 13);
	r_anal_bb_set_offset (first, 2, 16);

	second->ninstr = 4;
	r_anal_bb_set_offset (second, 0, 0);
	r_anal_bb_set_offset (second, 1, 4);
	r_anal_bb_set_offset (second, 2, 9);
	r_anal_bb_set_offset (second, 3, 30);

	bool success = r_anal_block_merge (first, second);
	assert_invariants (anal);
	mu_assert ("merge success", success);
	mu_assert_eq (blocks_count (anal), 1, "count after merge");
	mu_assert_eq (first->addr, 0x1337, "addr after merge");
	mu_assert_eq (first->size, 666, "size after merge");
	mu_assert_eq (first->jump, 0xdeadbeef, "jump after merge");
	mu_assert_eq (first->fail, 0xc0ffee, "fail after merge");

	mu_assert_eq (first->ninstr, 3+4, "ninstr after merge");
	mu_assert_eq (r_anal_bb_offset_inst (first, 0), 0, "offset 0 after merge");
	mu_assert_eq (r_anal_bb_offset_inst (first, 1), 13, "offset 1 after merge");
	mu_assert_eq (r_anal_bb_offset_inst (first, 2), 16, "offset 2 after merge");
	mu_assert_eq (r_anal_bb_offset_inst (first, 3), 42+0, "offset 3 after merge");
	mu_assert_eq (r_anal_bb_offset_inst (first, 4), 42+4, "offset 4 after merge");
	mu_assert_eq (r_anal_bb_offset_inst (first, 5), 42+9, "offset 5 after merge");
	mu_assert_eq (r_anal_bb_offset_inst (first, 6), 42+30, "offset 6 after merge");

	r_anal_block_unref (first);
	// second must be already freed by the merge!

	assert_invariants (anal);
	r_anal_free (anal);
	mu_end;
}

bool test_r_anal_block_merge_in_function() {
	RAnal *anal = r_anal_new ();
	assert_invariants (anal);

	RAnalFunction *fcn = r_anal_create_function (anal, "bbowner", 0x1337, 0, NULL);

	RAnalBlock *first = r_anal_create_block (anal, 0x1337, 42);
	RAnalBlock *second = r_anal_create_block (anal, 0x1337 + 42, 624);
	assert_invariants (anal);
	mu_assert_eq (blocks_count (anal), 2, "count after create");

	r_anal_function_add_block (fcn, first);
	assert_invariants (anal);
	r_anal_function_add_block (fcn, second);
	assert_invariants (anal);

	bool success = r_anal_block_merge (first, second);
	assert_invariants (anal);
	mu_assert ("merge success", success);
	mu_assert_eq (blocks_count (anal), 1, "count after merge");
	mu_assert_eq (r_list_length (fcn->bbs), 1, "fcn bbs after merge");
	mu_assert_eq (r_list_length (first->fcns), 1, "bb functions after merge");
	mu_assert ("function has merged block", r_list_contains (fcn->bbs, first));
	mu_assert ("merged block is in function", r_list_contains (first->fcns, fcn));

	r_anal_block_unref (first);
	// second must be already freed by the merge!

	assert_invariants (anal);
	r_anal_free (anal);
	mu_end;
}

bool test_r_anal_block_delete() {
	RAnal *anal = r_anal_new ();
	assert_invariants (anal);

	RAnalFunction *fcn = r_anal_create_function (anal, "bbowner", 0x1337, 0, NULL);

	RAnalBlock *block = r_anal_create_block (anal, 0x1337, 42);
	assert_invariants (anal);
	mu_assert_eq (blocks_count (anal), 1, "count after create");

	r_anal_function_add_block (fcn, block);
	assert_invariants (anal);
	mu_assert_eq (block->ref, 2, "refs after adding");
	mu_assert_eq (r_list_length (fcn->bbs), 1, "fcn bbs after add");
	mu_assert_eq (r_list_length (block->fcns), 1, "bb fcns after add");

	r_anal_delete_block (block);
	assert_invariants (anal);
	mu_assert_eq (block->ref, 1, "refs after delete");
	mu_assert_eq (r_list_length (fcn->bbs), 0, "fcn bbs after delete");
	mu_assert_eq (r_list_length (block->fcns), 0, "bb fcns after delete");

	r_anal_block_unref (block);

	r_anal_free (anal);
	mu_end;
}

bool test_r_anal_block_set_size() {
	RAnal *anal = r_anal_new ();
	assert_invariants (anal);

	RAnalFunction *fcn = r_anal_create_function (anal, "bbowner", 0x1337, 0, NULL);

	RAnalBlock *block = r_anal_create_block (anal, 0x1337, 42);
	assert_invariants (anal);

	r_anal_function_add_block (fcn, block);
	assert_invariants (anal);

	r_anal_block_set_size (block, 300);
	assert_invariants (anal);
	mu_assert_eq (block->size, 300, "size after set_size");

	RAnalBlock *second = r_anal_create_block (anal, 0x1337+300, 100);
	assert_invariants (anal);
	r_anal_function_add_block (fcn, block);
	assert_invariants (anal);
	r_anal_function_linear_size (fcn); // trigger lazy calculation of min/max cache
	assert_invariants (anal);

	r_anal_block_set_size (second, 500);
	assert_invariants (anal);
	mu_assert_eq (second->size, 500, "size after set_size");

	r_anal_block_set_size (block, 80);
	assert_invariants (anal);
	mu_assert_eq (block->size, 80, "size after set_size");

	r_anal_block_unref (block);
	r_anal_block_unref (second);
	assert_invariants (anal);

	r_anal_free (anal);
	mu_end;
}

bool test_r_anal_block_relocate() {
	RAnal *anal = r_anal_new ();
	assert_invariants (anal);

	RAnalFunction *fcn = r_anal_create_function (anal, "bbowner", 0x1337, 0, NULL);

	RAnalBlock *block = r_anal_create_block (anal, 0x1337, 42);
	assert_invariants (anal);

	r_anal_function_add_block (fcn, block);
	assert_invariants (anal);
	r_anal_function_linear_size (fcn); // trigger lazy calculation of min/max cache
	assert_invariants (anal);

	bool success = r_anal_block_relocate (block, 0x200, 0x100);
	mu_assert ("relocate success", success);
	assert_invariants (anal);
	mu_assert_eq (block->addr, 0x200, "addr after relocate");
	mu_assert_eq (block->size, 0x100, "size after relocate");

	RAnalBlock *second = r_anal_create_block (anal, 0x1337+300, 100);
	assert_invariants (anal);
	r_anal_function_add_block (fcn, second);
	assert_invariants (anal);

	success = r_anal_block_relocate (second, 0x400, 0x123);
	mu_assert ("relocate success", success);
	assert_invariants (anal);
	mu_assert_eq (second->addr, 0x400, "addr after relocate");
	mu_assert_eq (second->size, 0x123, "size after relocate");
	r_anal_function_linear_size (fcn); // trigger lazy calculation of min/max cache
	assert_invariants (anal);

	success = r_anal_block_relocate (block, 0x400, 0x333);
	mu_assert ("relocate fail on same addr", !success);
	assert_invariants (anal);
	mu_assert_eq (block->addr, 0x200, "addr after failed relocate");
	mu_assert_eq (block->size, 0x100, "size after failed relocate");
	r_anal_function_linear_size (fcn); // trigger lazy calculation of min/max cache
	assert_invariants (anal);

	// jump after the other block
	success = r_anal_block_relocate (block, 0x500, 0x333);
	mu_assert ("relocate success", success);
	assert_invariants (anal);
	mu_assert_eq (block->addr, 0x500, "addr after failed relocate");
	mu_assert_eq (block->size, 0x333, "size after failed relocate");
	r_anal_function_linear_size (fcn); // trigger lazy calculation of min/max cache
	assert_invariants (anal);

	// jump before the other block
	success = r_anal_block_relocate (block, 0x10, 0x333);
	mu_assert ("relocate success", success);
	assert_invariants (anal);
	mu_assert_eq (block->addr, 0x10, "addr after failed relocate");
	mu_assert_eq (block->size, 0x333, "size after failed relocate");

	r_anal_block_unref (block);
	r_anal_block_unref (second);
	assert_invariants (anal);

	r_anal_free (anal);
	mu_end;
}

int all_tests() {
	mu_run_test (test_r_anal_block_create);
	mu_run_test (test_r_anal_block_contains);
	mu_run_test (test_r_anal_block_split);
	mu_run_test (test_r_anal_block_split_in_function);
	mu_run_test (test_r_anal_block_merge);
	mu_run_test (test_r_anal_block_merge_in_function);
	mu_run_test (test_r_anal_block_delete);
	mu_run_test (test_r_anal_block_set_size);
	mu_run_test (test_r_anal_block_relocate);
	return tests_passed != tests_run;
}

int main(int argc, char **argv) {
	return all_tests();
}
