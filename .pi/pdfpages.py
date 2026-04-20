import sys, re
from pathlib import Path

for path in sys.argv[1:]:
    data = Path(path).read_bytes()
    pages = len(re.findall(rb'/Type\s*/Page[\s/>]', data))
    counts = re.findall(rb'/Count\s+(\d+)', data)
    cntmax = max([int(c) for c in counts], default=0)
    print(f"{path}: type_page={pages}  max_count={cntmax}")
