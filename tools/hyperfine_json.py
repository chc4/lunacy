"""A hyperfine JSON export's results, as hyperfine 1 wrote them, whichever version wrote it.

hyperfine 2 (`schema_version` 2) names each result `name` (its `-n`), keeps the command in
`command`, and gives each run's measurements and a summary of each metric, wall time the one
this project compares. Each result here is hyperfine 1's: `command` the name, `times` each run's
wall time in seconds, its `mean`, `stddev`, `median`, `min` and `max`, `exit_codes`, and
`parameters` for a parameter scan.
"""
import json


def results(path_or_text, text=False):
    data = json.loads(path_or_text) if text else json.load(open(path_or_text))
    if data.get('schema_version', 1) < 2:
        return data['results']
    return [v1(r) for r in data['results']]


def v1(r):
    wall = r['summary']['time_wall_clock']
    out = {
        'command': r.get('name') or r['command'],
        'times': [m['time_wall_clock']['value'] for m in r['measurements']],
        'exit_codes': [m.get('exit_code', 0) for m in r['measurements']],
        'mean': wall['mean'], 'stddev': wall['stddev'], 'median': wall['median'],
        'min': wall['min'], 'max': wall['max'],
    }
    if 'parameters' in r:
        out['parameters'] = r['parameters']
    return out
