module zeroofone.tool.sorted_list;

int binarySearch(alias compare, T, U, V)(const T[] sortedList, const U elem, const V other, out size_t result) @safe {
	int cmp;
	size_t currentMin, currentMax;
	/* This is a binary search. */

	if (sortedList.length == 0) {
		result = 0;

		return -1;
	}

	currentMin = 0;

	currentMax = sortedList.length - 1;

	for (;;) {
		/* FIXME: overflow-safe? */
		/* No: (and (> currentMin (/ Max 2)) (> currentMax (/ Max 2))) */
		size_t i = ((currentMin + currentMax) / 2);

		if (i == sortedList.length) {
			/* FIXME: I don't see how this one can be true */
			result = sortedList.length;

			return -1;
		}

		cmp = compare(elem, sortedList[i], other);

		if (cmp > 0) {
			if ((currentMin > currentMax)) {
				result = (i + 1);

				return -1;
			}

			/* FIXME: overflow-safe? */
			currentMin = (i + 1);
		}
		else if (cmp < 0) {
			if ((currentMin > currentMax) || (i == 0)) {
				result = i;

				return -1;
			}

			/* overflow-safe */
			currentMax = (i - 1);
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
	assert(binarySearch!testCmpFunc(arr, arr[3], arr[3], result) == 0);
	assert(result == 3);
}
