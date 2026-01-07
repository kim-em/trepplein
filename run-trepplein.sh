#!/bin/bash
# Wrapper to run trepplein that stops on error
# Usage: ./run-trepplein.sh [export-file] [max-lines]
#
# This script runs sbt and stops early when:
# - A StackOverflowError is detected
# - Other Java exceptions are detected
# - max-lines of output have been shown (default 100)

EXPORT_FILE="${1:-/tmp/init.export}"
MAX_LINES="${2:-100}"

cd "$(dirname "$0")"

# Create a temp file for output
OUTFILE=$(mktemp)

# Run sbt in background with increased stack size
# -Xss100m is needed for large export files like Init
sbt -J-Xss100m --error "run $EXPORT_FILE" 2>&1 > "$OUTFILE" &
SBT_PID=$!

# Monitor output
LINES=0
ERROR_SEEN=0
while kill -0 $SBT_PID 2>/dev/null; do
    # Read new lines from output
    NEWLINES=$(tail -n +$((LINES+1)) "$OUTFILE" 2>/dev/null)
    if [ -n "$NEWLINES" ]; then
        echo "$NEWLINES"
        LINES=$(wc -l < "$OUTFILE")

        # Check for errors
        if echo "$NEWLINES" | grep -q "StackOverflowError\|java.lang.Exception\|FATAL:\|OutOfMemoryError\|iterations limit"; then
            ERROR_SEEN=1
            # Show a few more lines for context
            sleep 1
            tail -n +$((LINES+1)) "$OUTFILE" 2>/dev/null | head -10
            echo "--- Killing sbt due to error ---"
            kill $SBT_PID 2>/dev/null
            # Also kill any child java processes
            pkill -P $SBT_PID 2>/dev/null
            break
        fi

        # Check line limit
        if [ $LINES -ge $MAX_LINES ]; then
            echo "--- Reached $MAX_LINES lines, stopping ---"
            kill $SBT_PID 2>/dev/null
            pkill -P $SBT_PID 2>/dev/null
            break
        fi
    fi
    sleep 0.2
done

# Wait for sbt to exit
wait $SBT_PID 2>/dev/null
EXIT_CODE=$?

rm -f "$OUTFILE"

if [ $ERROR_SEEN -eq 1 ]; then
    exit 1
fi
exit $EXIT_CODE
