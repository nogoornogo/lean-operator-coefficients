#!/usr/bin/env python3
"""Print a progress-instrumented Lean probe; never a proof oracle.

Build SMB1WeakCountArithmetic before the connection probe. The counts probe
checks only the old finite-count lemma, never the old stopped whole module.
Run printed source through the existing guarded kernel runner, serially.
"""
import argparse
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('stage',choices=['counts','connection'])
    parser.add_argument('--progress',required=True,type=Path)
    args = parser.parse_args()
    def marker(name):
        return 'run_cmd do IO.FS.writeFile '+json.dumps(str(args.progress))+' '+json.dumps(name)+'\n\n'
    if args.stage == 'counts':
        old=(ROOT/'tools/structural-support/probes/b1-weak-envelope-stopped.lean.txt').read_text()
        a=old.index('private theorem weak_bound_counts')
        b=old.index('/-- Complementary weak',a)
        print('import Physics.StandardModel.Operators.SMB1DimensionBounds\nnamespace GUT.SMB1WeakLocalization\nopen Math DeltaLOneSignedInput\nopen scoped BigOperators\n')
        print(marker('before-counts')+old[a:b].replace('private theorem','theorem')+marker('counts-passed'))
        print('end GUT.SMB1WeakLocalization')
    else:
        source=(ROOT/'Physics/StandardModel/Operators/SMB1WeakDimensionBounds.lean').read_text()
        source=re.sub(r'/--[\s\S]*?-/\n','',source)
        source=re.sub(r'^theorem (\w+)',lambda m:marker('before-'+m.group(1))+m.group(0),source,flags=re.M)
        source=source.replace('end GUT.SMB1WeakDimensionBounds',marker('connection-end-reached')+'end GUT.SMB1WeakDimensionBounds')
        print(source,end='')

if __name__=='__main__':
    main()
