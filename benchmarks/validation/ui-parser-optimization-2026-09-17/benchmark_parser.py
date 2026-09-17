import csv, importlib.util, json, statistics, sys, time
from pathlib import Path
root=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(root/'src'))
from bae_bertini import continuation as new
spec=importlib.util.spec_from_file_location('parser_before', Path(__file__).with_name('parser_before.py'))
old=importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
source=root/'examples/continuation/initial_data_70.csv'
new.bertini.default_precision(100)
kwargs=dict(input_path=source,lambda_column='lambda0',parameter_symbol='h',target_value='0',path_symbol='t')
from unittest.mock import patch
with patch.object(new, 'parse_expression', old.parse_expression):
 a=new.load_problem(**kwargs)
b=new.load_problem(**kwargs)
assert a[1]==b[1]
assert repr(a[4])==repr(b[4])
for t in ('0','0.5','1'):
 assert repr(a[3].eval(a[4],new.bertini.multiprec.Complex(t)))==repr(b[3].eval(b[4],new.bertini.multiprec.Complex(t)))
optimized_parser=new.parse_expression
measurements={'before':[],'after':[]}
for _ in range(7):
 for name, mod in [('before',old),('after',new)]:
  start=time.perf_counter()
  with patch.object(new, 'parse_expression', old.parse_expression if name == 'before' else optimized_parser):
   new.load_problem(**kwargs)
  measurements[name].append(time.perf_counter()-start)
medians={k:statistics.median(v) for k,v in measurements.items()}
result=dict(input='examples/continuation/initial_data_70.csv',equations=len(a[0]),expression_characters=sum(len(r['expression']) for r in a[0]),precision=100,load_problem_seconds=measurements,median_seconds=medians,speedup=medians['before']/medians['after'],system_evaluations_identical_at=['0','0.5','1'])
(root/'benchmarks/validation/ui-parser-optimization-2026-09-17/parser-benchmark.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
