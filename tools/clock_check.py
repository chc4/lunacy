"""Whether the monotonic clock is fine enough to time benchmarks with.

Reads the clock back to back for a fifth of a second and prints how many times its value changed
and its longest step. A healthy clock changes every read, a few hundred nanoseconds apart in this
loop, with a step of tens of microseconds where the process was interrupted. A coarse one moves
only at the kernel's timer tick, a millisecond or more apart, for some or all of the time, so
timings taken with it are rounded to whole milliseconds. Exits with 1 when it is coarse.

The process being descheduled during a read makes a long step too, so it reads up to `TRIES`
times and the clock is fine if any read is: a coarse clock is coarse every time.
"""

import sys
import time

# Fewer changes than this in `SPAN_NS` is a coarse clock: a healthy one makes hundreds of
# thousands, a coarse one a few hundred at most.
MIN_CHANGES = 10_000
SPAN_NS = 200_000_000
# A step this long is the clock stopping between ticks, not the process interrupted, which shows
# as tens of microseconds.
MAX_STEP_NS = 2_000_000
TRIES = 3


def read():
    steps = []
    last = time.perf_counter_ns()
    end = last + SPAN_NS
    while last < end:
        now = time.perf_counter_ns()
        if now != last:
            steps.append(now - last)
            last = now
    ok = len(steps) >= MIN_CHANGES and max(steps) < MAX_STEP_NS
    print(f"clock: {len(steps)} changes in {SPAN_NS // 1_000_000} ms, longest step {max(steps) / 1000:.1f} us: {'fine' if ok else 'COARSE'}")
    return ok


def main():
    if any(read() for _ in range(TRIES)):
        return 0
    print("clock: too coarse to time benchmarks with, timings would be whole milliseconds", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
