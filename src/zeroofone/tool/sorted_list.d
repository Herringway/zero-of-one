module zeroofone.tool.sorted_list;

bool binarySearch(alias compare, T, U, V)(const T[] sortedList, const U elem, const V other, out size_t result) @safe {
	int cmp;
	size_t currentMin, currentMax;

	if (sortedList.length == 0) {
		result = 0;

		return false;
	}

	currentMax = sortedList.length - 1;

	for (;;) {
		/* FIXME: overflow-safe? */
		/* No: (and (> currentMin (/ Max 2)) (> currentMax (/ Max 2))) */
		const size_t i = ((currentMin + currentMax) / 2);

		if (i == sortedList.length) {
			/* FIXME: I don't see how this one can be true */
			result = sortedList.length;

			return false;
		}

		cmp = compare(elem, sortedList[i], other);

		if (cmp > 0) {
			if ((currentMin > currentMax)) {
				result = (i + 1);

				return false;
			}

			/* FIXME: overflow-safe? */
			currentMin = (i + 1);
		} else if (cmp < 0) {
			if ((currentMin > currentMax) || (i == 0)) {
				result = i;

				return false;
			}

			/* overflow-safe */
			currentMax = (i - 1);
		} else {
			result = i;

			return true;
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
	immutable arr = [1, 2, 4, 6, 8];
	{
		size_t result;
		assert(binarySearch!testCmpFunc(arr, arr[3], arr[3], result));
		assert(result == 3);
	}
	{
		size_t result;
		assert(!binarySearch!testCmpFunc(arr, 3, arr[3], result));
		assert(result == 2);
	}
}
