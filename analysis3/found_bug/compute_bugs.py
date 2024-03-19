import time
import os
import csv
import numpy as np

group = ["elementary", "complex", "diffAndInteg", "cdf", "solveEqu", "compAndopt", "sf"]
solver_type = ["smt", "bitwuzla", "mathsat5", "dreal-is", "cvc5-real", "fp2int", "jfs", "gosat", "smt-dreal"]

# group = ["elementary", "complex", "diffAndInteg", "cdf", "solveEqu", "sf"]
# solver_type = ["smt", "bitwuzla", "mathsat5", "dreal-is", "cvc5-real", "jfs", "gosat", "smt-dreal", "smt-jfs"]

def get_bug(stype):
  data = {}
  for file in group:
    data[file] = []
    for solver in solver_type:
      # "find ../benchmark3/elementary -type f -name "*&smt&*" -name "*bfs.runlog" -exec grep -n "FloatPointCheck: " {} \;" % (file, stype, solver)
      cmdStr = "find ../benchmark3/%s -type f -name \"*&%s&*\" -name \"*%s.runlog\" -exec grep -n \"FloatPointCheck: \" {} \;" % (file, solver, stype)
      with os.popen(cmdStr, 'r') as f:
        resAll = f.read()
      if resAll == "":
        continue
      resList = resAll.split('\n')

      resVec = [0, 0, 0, 0, 0, 0]
      uniqOver = []
      uniqUnder = []
      uniqInvalid = []
      uniqZero = []
      uniqAccuray = []
      for i in range(len(resList)):
        lineStr = resList[i]
        if "libm" in lineStr:
          continue
        if "FloatPointCheck" not in lineStr:
          continue
        resVec[-1] += 1
        locStr = lineStr.split("KLEE: ERROR: ")[1].split(": FloatPointCheck:")[0]
        if "Overflow found" in lineStr:
          resVec[0] += 1
          if locStr not in uniqOver:
            uniqOver.append(locStr)
        if "Underflow found" in lineStr:
          resVec[1] += 1
          if locStr not in uniqUnder:
            uniqUnder.append(locStr)
        if "Invalid found" in lineStr:
          resVec[2] += 1
          if locStr not in uniqInvalid:
            uniqInvalid.append(locStr)
        if "Zero found" in lineStr:
          resVec[3] += 1
          if locStr not in uniqZero:
            uniqZero.append(locStr)
        if "Accuracy found" in lineStr:
          resVec[4] += 1
          if locStr not in uniqAccuray:
            uniqAccuray.append(locStr)

      print("======", stype, file, solver, "======")
      # data[file].append(resVec)
      print(resVec)
      # print(len(uniqOver), len(uniqUnder), len(uniqInvalid), len(uniqZero))
      # 通个求解器可能在多个程序能测出相同的bug，所以要去重，因为可能多个程序调用了相同函数中的bug
      uniqVec = [len(uniqOver), len(uniqUnder), len(uniqZero), len(uniqInvalid), len(uniqAccuray)]
      uniqVec.append(np.sum(uniqVec))
      print(uniqVec)
      data[file].append(uniqVec)

  return data

databfs = get_bug("bfs")
bug_file = "uniq_bug_result_bfs1.csv"
with open(bug_file, 'w', newline='') as file:
  writer = csv.writer(file)
  for key in databfs.keys():
    for datav in databfs[key]:
      writer.writerows([datav])
print(f'数据已写入CSV文件: {bug_file}')

datadfs = get_bug("dfs")
bug_file = "uniq_bug_result_dfs1.csv"
with open(bug_file, 'w', newline='') as file:
  writer = csv.writer(file)
  for key in datadfs.keys():
    for datav in datadfs[key]:
      writer.writerows([datav])
print(f'数据已写入CSV文件: {bug_file}')
