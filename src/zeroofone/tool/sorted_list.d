module zeroofone.tool.sorted_list;

import zeroofone.pervasive;

int ZoO_sorted_list_index_of(alias compare, T, U, V)(const T[] sorted_list, const U elem, const V other, out size_t result) @safe {
	int cmp;
	size_t current_min, current_max;
	/* This is a binary search. */

	if (sorted_list.length == 0) {
		result = 0;

		return -1;
	}

	current_min = 0;

	current_max = sorted_list.length - 1;

	for (;;) {
		/* FIXME: overflow-safe? */
		/* No: (and (> current_min (/ Max 2)) (> current_max (/ Max 2))) */
		size_t i = ((current_min + current_max) / 2);

		if (i == sorted_list.length) {
			/* FIXME: I don't see how this one can be true */
			result = sorted_list.length;

			return -1;
		}

		cmp = compare(elem, sorted_list[i], other);

		if (cmp > 0) {
			if ((current_min > current_max)) {
				result = (i + 1);

				return -1;
			}

			/* FIXME: overflow-safe? */
			current_min = (i + 1);
		}
		else if (cmp < 0) {
			if ((current_min > current_max) || (i == 0)) {
				result = i;

				return -1;
			}

			/* overflow-safe */
			current_max = (i - 1);
		}
		else {
			result = i;

			return 0;
		}
	}
}


@safe pure unittest {
	static int testCmpFunc(const int a, const int b, const int) @safe pure {
		if (a > b) {
			return 1;
		} else if (a < b) {
			return -1;
		} else {
			return 0;
		}
	}
	auto arr = [1, 2, 4, 6, 8];
	size_t result;
	assert(ZoO_sorted_list_index_of!testCmpFunc(arr, arr[3], arr[3], result) == 0);
	assert(result == 3);
}
