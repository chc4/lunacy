#!/usr/bin/env python3
"""The IBS samples whose op had one of IBS's op data flags set.

    perf report -D -i DATA | tools/ibs_samples.py FLAG DATA > SAMPLES

FLAG is a flag as perf decodes IBS's op data (`DcMisAcc`, a misaligned access; `DcMiss`).
DATA is a `perf record -R -e ibs_op//` recording: its decoded dump on stdin says which samples
have the flag, and its `perf script` names their functions. Writes those samples as
`perf script -F ip,sym` does, for tools/jit_samples.py, and to stderr how many there were and,
of those that accessed data, the data address's offset in its cache line.
"""
import collections
import re
import subprocess
import sys


def main():
    flag, data = sys.argv[1], sys.argv[2]
    # A sample's decoded IBS registers come before its record, which has its time.
    flagged, set_, address = {}, False, None
    for line in sys.stdin:
        if line.startswith('ibs_op_data3:'):
            m = re.search(rf'\b{flag} (\d)', line)
            if not m:
                sys.exit(f'{flag}: not a flag of the op data perf decodes')
            set_, address = m.group(1) == '1', None
        elif line.startswith('IbsDCLinAd:'):
            address = int(line.split()[1], 16)
        elif 'PERF_RECORD_SAMPLE' in line:
            if set_:
                flagged[int(line.split()[1])] = address
            set_, address = False, None
    script = subprocess.run(['perf', 'script', '-i', data, '--ns', '-F', 'time,ip,sym'],
                            capture_output=True, text=True, check=True).stdout
    total = 0
    for line in script.splitlines():
        time, _, rest = line.strip().partition(': ')
        seconds, _, nanos = time.partition('.')
        if int(seconds) * 10**9 + int(nanos) in flagged:
            print(' ' + rest.strip())
            total += 1
    offsets = collections.Counter(a % 64 for a in flagged.values() if a is not None)
    print(f'{total} samples with {flag}; data address offsets in the cache line: '
          + ', '.join(f'{o}: {n}' for o, n in sorted(offsets.items())), file=sys.stderr)


main()
