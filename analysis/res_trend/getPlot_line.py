import numpy as np
import matplotlib.pyplot as plt
import csv


class bench_cov:
  def __init__(self, bench_type, bench_name, solver_type, search_type):
    self.bench_type = bench_type
    self.bench_name = bench_name
    self.solver_type = solver_type
    self.search_type = search_type
    self.coverage_trend = []
    self.covline_trend = []

  def updateCoverage(self,sec,coverage):
    if len(self.coverage_trend) == 0:
      self.coverage_trend.append((sec,coverage))
      return
    if coverage > self.coverage_trend[-1][1]: # 是否是一个合适的数据，更新数据
      if sec == self.covline_trend[-1][0]:
        self.coverage_trend.pop()
      self.coverage_trend.append((sec,coverage))

  def updateCovline(self,sec,covline):
    if len(self.covline_trend) == 0:
      self.covline_trend.append((sec, covline))
      return
    if covline > self.covline_trend[-1][1]:
      if sec == self.covline_trend[-1][0]:
        self.covline_trend.pop()
      self.covline_trend.append((sec,covline)) # update item

  def printCovline(self):
    print(self.bench_name)
    for it in self.covline_trend:
      print(it[0],it[1])

def getDate():
  driver_tag = "=== TestCase : "
  end_tag = "=== End"
  
  trend_file = "cov_trend_2.txt"
  bench_res = []
  flag = False
  
  with open(trend_file, 'r') as log:
    for line in log:
      if line.find(driver_tag) != -1:
        case_name = line.split(driver_tag)[1].replace('\n', '')
        strList = case_name.split(",")
        strName = strList[0].strip().split("&")
        class_name = strName[0]
        driver_name = strName[1]
        solver_type = strName[2]
        search_type = strName[3][:3]
  
        driver_bench = bench_cov(class_name, driver_name, solver_type, search_type)
        flag = True
        continue
  
      elif line.find(end_tag) != -1:
        if flag:
          bench_res.append(driver_bench)
        driver_name = ""
        flag = 0
        continue
          
      else:
        if len(line.split(',')) != 4:
          continue
        sec,coverage,covline,covbranch = line.split(',')
        if len(sec) > 0:
          sec = int(sec)
          coverage = float(coverage)
          if covline=="\n" or covline=="":
            covline = 0
          else:
            covline = int(covline)

          #print(driver_name,sec,coverage,covline)
          driver_bench.updateCoverage(sec,coverage)
          driver_bench.updateCovline(sec,covline)
  return bench_res


def f_line(ax, dataX, dataY, marker, label, color, cname):
  for i in range(len(dataX)):
    ax.plot(np.array(dataX[i]), np.array(dataY[i]),
            marker=marker[i],
            markersize=None,
            markerfacecolor=None,
            markeredgecolor=None,
            alpha=0.5,
            ls=None,
            label=label[i],
            linewidth=2,
            c=color[i])

  ax.tick_params(right=True, top=True)
  ax.spines['bottom'].set_linewidth(0.1)
  ax.spines['left'].set_linewidth(0.1)
  ax.spines['right'].set_linewidth(0.1)
  ax.spines['top'].set_linewidth(0.1)
  ax.tick_params(direction='in', labelsize=12)
  ax.set_xlabel("Elapsed Timed (min)", fontsize=12)
  ax.set_ylabel("Total LoCC", fontsize=12)
  ax.legend(bbox_to_anchor=(0.5, 1.2), loc='upper center', ncol=3)


def writeDate(cname, stype, search_type, bench_res):
  #class_name*solver_type*search_type=72*2
  sec_time = 3750
  cov_trend_list = []

  pre_covline = 0
  curr_covline = 0
  for time_pos in range(sec_time):
    if time_pos == sec_time - 1:
      cov_trend_list.append((time_pos, curr_covline))
      break
    curr_covline = 0
    for it in bench_res:
      if it.bench_type != cname or it.solver_type != stype or it.search_type != search_type:
        continue
      item_curr_covline = 0
      for sec, covline in it.covline_trend:
        if sec > time_pos:
          break
        item_curr_covline = covline
      #print(it.bench_name,item_curr_covline)
      curr_covline += item_curr_covline
    
    if curr_covline != pre_covline:
      cov_trend_list.append((time_pos,curr_covline))
      pre_covline = curr_covline

  Xdata = []
  Ydata = []
  for it in cov_trend_list:
      minus = it[0] / 60
      Xdata.append(minus)
      Ydata.append(it[1])

  return Xdata, Ydata


if __name__ == "__main__":

  bench_res = getDate()

  class_name = ["elementary", "algorithm", "sf"]

  solver_type = ["smt", "bitwuzla", "mathsat5", "dreal-is", "cvc5-real", "fp2int", "jfs", "gosat", "smt-dreal"]

  for cname in class_name:
    dataXBfs = []
    dataYBfs = []
    dataXDfs = []
    dataYDfs = []
    for stype in solver_type:
      Xdata, Ydata = writeDate(cname, stype, "bfs", bench_res)
      dataXBfs.append(Xdata)
      dataYBfs.append(Ydata)

      Xdata, Ydata = writeDate(cname, stype, "dfs", bench_res)
      dataXDfs.append(Xdata)
      dataYDfs.append(Ydata)

    csv_trend_bfs = "csv_lines/"+cname+"_trend_lines_bfs_2.csv"
    with open(csv_trend_bfs, 'w', newline='') as file:
      writer = csv.writer(file)
      for i in range(len(dataXBfs)):
        writer.writerows([dataXBfs[i]])
        writer.writerows([dataYBfs[i]])
    print(f'write lines into {csv_trend_bfs}.')

    csv_trend_dfs = "csv_lines/"+cname+"_trend_lines_dfs_2.csv"
    with open(csv_trend_dfs, 'w', newline='') as file:
      writer = csv.writer(file)
      for i in range(len(dataXDfs)):
        writer.writerows([dataXDfs[i]])
        writer.writerows([dataYDfs[i]])
    print(f'write lines into {csv_trend_dfs}.')
