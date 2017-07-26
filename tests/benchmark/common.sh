#
# This file is meant to be sourced from other tests scripts.
#

cleanup() {
	if [ x"$TMPFILE" != "x" ]; then
		rm -f "$TMPFILE"
	fi

	# Call the tap.sh exit cleanup code
	_exit
}

xseq() {
	i=$1
	while [[ "$i" -le "$2" ]]; do
		echo "$i"
		i=$(( i + 1 ))
	done
}

# Set TEST_TIME_BIN
if [ -x "$URCU_TEST_TIME_BIN" ]; then
	TEST_TIME_BIN="$URCU_TEST_TIME_BIN"
elif [ -x "/usr/bin/time" ]; then
	TEST_TIME_BIN="/usr/bin/time"
else
	TEST_TIME_BIN=""
fi
export TEST_TIME_BIN

# Create a temporary file for tests output
TMPFILE=$(mktemp)

# Set traps to delete the temporary file on exit
trap cleanup EXIT
