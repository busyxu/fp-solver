import time
import os
import csv
import re

group = ["elementary", "complex", "diffAndInteg", "blas", "cdf", "solveEqu", "compAndopt", "sf"]
solver_type = ["smt", "bitwuzla", "mathsat5", "dreal-is", "cvc5-real", "fp2int", "jfs", "gosat", "smt-dreal"]


def get_bug(stype):
  data = {}
  for file in group:
    data[file] = []
    for solver in solver_type:
      cmdStr = "find ../benchmark3/%s -type f -name \"*&%s*\" -name \"*&%s*\" -name \"*.runlog\" -exec grep -n \"KLEE: WARNING: \" {} \;" % (file, stype, solver)
      with os.popen(cmdStr, 'r') as f:
        resAll = f.read()
      if resAll == "":
        continue
      resList = resAll.split('\n')

      '''
      MathSAT5: MathSAT5 solving SAT and evaluation SUCCESS !
      MathSAT5: MathSAT5 solving SAT and evaluate FAILURE and remove the state !
      MathSAT5: MathSAT5 solving UNSAT and evaluate FAILURE and remove the state !
      MathSAT5: MathSAT5 solving UNKNOWN and evaluate FAILURE and remove the state !
      '''
      resVec = [0, 0, 0, 0, 0]

      for i in range(len(resList)):
        lineStr = resList[i]
        if re.search(r"SAT.*S", lineStr):
          resVec[0] += 1
        elif re.search(r"SAT.*F", lineStr):
          resVec[1] += 1
        elif re.search(r"UNSAT.*F", lineStr):
          resVec[2] += 1
        elif re.search(r"UNKNOWN.*F", lineStr):
          resVec[3] += 1

      resVec[-1] = resVec[0]+resVec[1]+resVec[2]+resVec[3]
      print("======", stype, file, solver, "======")
      data[file].append(resVec)
      print(resVec)

  return data

databfs = get_bug("bfs")
bug_file = "info_bfs.csv"
with open(bug_file, 'w', newline='') as file:
  writer = csv.writer(file)
  for key in databfs.keys():
    for datav in databfs[key]:
      writer.writerows([datav])
print(f'数据已写入CSV文件: {bug_file}')

datadfs = get_bug("dfs")
bug_file = "info_dfs.csv"
with open(bug_file, 'w', newline='') as file:
  writer = csv.writer(file)
  for key in datadfs.keys():
    for datav in datadfs[key]:
      writer.writerows([datav])
print(f'数据已写入CSV文件: {bug_file}')
