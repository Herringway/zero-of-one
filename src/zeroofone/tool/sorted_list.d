module zeroofone.tool.sorted_list;

bool binarySearch(alias compare, T, U, V)(const T[] sortedList, const U elem, const V other, out size_t result) @safe
out(; result <= sortedList.length)
{
	size_t currentMin, currentMax;

	if (sortedList.length == 0) {
		result = 0;
		return false;
	}

	currentMax = sortedList.length - 1;

	for (;;) {
		result = ((currentMin + currentMax) / 2);

		if (result == sortedList.length) {
			return false;
		}

		const cmp = compare(elem, sortedList[result], other);

		if (cmp > 0) {
			if ((currentMin > currentMax)) {
				result++;

				return false;
			}
			currentMin = (result + 1);
		} else if (cmp < 0) {
			if ((currentMin > currentMax) || (result == 0)) {
				return false;
			}
			currentMax = (result - 1);
		} else {
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
