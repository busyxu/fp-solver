import numpy as np
import matplotlib.pyplot as plt


class bench_cov:
  def __init__(self, bench_type, bench_name, solver_type, search_type):
    self.bench_type = bench_type
    self.bench_name = bench_name
    self.solver_type = solver_type
    self.search_type = search_type
    self.coverage_trend = []
    self.covline_trend = [] #covline is branch cover

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
  
  #method_list = ["smt","jfs","dreal_jfs","vmcai","gosat","smt_dreal"]
  method_list = ["is"]
  
  trend_file = "cov_trend_1.txt"
  #trend_file = "test.txt"
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
          if covbranch=="\n" or covbranch=="":
            covbranch = 0
          else:
            covbranch = int(covbranch)

          #print(driver_name,sec,coverage,covline)
          driver_bench.updateCoverage(sec,coverage)
          driver_bench.updateCovline(sec,covbranch)

        # pre_sec = sec
        # pre_coverage = coverage
        # pre_covline = covline

  return bench_res

def f_line(ax, dataX, dataY, marker, label, color, cname):
  # 可扩展处  可自己添加画图数据
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
  # 画框设置
  # ax.spines['right'].set_visible(False)
  # ax.spines['top'].set_visible(False)
  ax.tick_params(right=True, top=True)
  ax.spines['bottom'].set_linewidth(0.1)
  ax.spines['left'].set_linewidth(0.1)
  ax.spines['right'].set_linewidth(0.1)
  ax.spines['top'].set_linewidth(0.1)
  # 参数设置
  ax.tick_params(direction='in', labelsize=12)
  # 坐标轴标签设置
  ax.set_xlabel("Elapsed Timed (min)", fontsize=12)
  ax.set_ylabel("Total NoBC", fontsize=12)
  # ax.set_ylim(0, 20000)
  # # 设置横轴标签设置
  # NUM = 7
  # index = np.linspace(0, data[0].shape[0] - 1, NUM, dtype=int)
  # ax.set_xticks(index, ['the' + str(i) for i in index])
  # 图例设置
  # ax.legend(fontsize=12, edgecolor='black', loc='lower right', ncol=3)
  ax.legend(bbox_to_anchor=(0.5, 1.2), loc='upper center', ncol=3)
  # if cname == "sf":
  #   # ax.legend(fontsize=12, edgecolor='black')
  #   ax.legend(bbox_to_anchor=(1.05, 1), loc=2, borderaxespad=0)
  # else:
    # ax.legend.remove()


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
    #print("=====",curr_covline)

  '''
  write into .dat
  '''
  # res_file = "datyx/" + class_name + "_" + solver_type + "_" + search_type + "_" + "covtrend.dat"
  # with open(res_file, 'w') as f:
  #   for it in cov_trend_list:
  #     # print(it[0],",",it[1])
  #     minus = it[0] / 60
  #     str_data = str(minus) + " " + str(it[1]) + '\n'
  #     f.write(str_data)

  '''
  drectry draw figure
  '''
  Xdata = []
  Ydata = []
  for it in cov_trend_list:
      minus = it[0] / 60
      Xdata.append(minus)
      Ydata.append(it[1])
      # if cname == "elementary" and stype == 'smt-dreal':
      #   Ydata.append(it[1]+20)
      # elif cname == "algorithm" and stype == 'smt-dreal':
      #   Ydata.append(it[1]+200)
      # else:
      #   Ydata.append(it[1])

  return Xdata, Ydata


if __name__ == "__main__":

  bench_res = getDate()

  class_name = ["elementary", "algorithm", "sf"]
  # class_name = ["elementary"]
  # class_name = ["algorithm"]
  # class_name = ["elementary", "diffAndInteg", "cdf", "solveEqu", "compAndopt", "sf"]
  # solver_type = ["smt", "bitwuzla", "mathsat5", "dreal-is", "cvc5-real", "fp2int", "jfs", "gosat", "smt-dreal", "smt-jfs"]
  solver_type = ["smt", "bitwuzla", "mathsat5", "dreal-is", "cvc5-real", "fp2int", "jfs", "gosat", "smt-dreal"]

  for cname in class_name:
    dataXBfs = []  # 数据序列参数
    dataYBfs = []
    dataXDfs = []  # 数据序列参数
    dataYDfs = []
    for stype in solver_type:
      Xdata, Ydata = writeDate(cname, stype, "bfs", bench_res)
      if stype == 'smt-dreal':
        # import itertools
        # merged_array = [max(a, b) for a, b in itertools.zip_longest(Ydata, dataYDfs[1], fillvalue=float('-inf'))]
        # if dataYDfs[1][-1] > Ydata[-1]:
        #   Ydata[-1] = dataYDfs[1][-1]
        dataXBfs.append(Xdata)
        dataYBfs.append(Ydata)
      else:
        dataXBfs.append(Xdata)
        dataYBfs.append(Ydata)
      Xdata, Ydata = writeDate(cname, stype, "dfs", bench_res)
      if stype == 'smt-dreal':
        # import itertools
        # merged_array = [max(a, b) for a, b in itertools.zip_longest(Ydata, dataYDfs[1], fillvalue=float('-inf'))]
        # if dataYDfs[1][-1] > Ydata[-1]:
        #   Ydata[-1] = dataYDfs[1][-1]
        dataXDfs.append(Xdata)
        dataYDfs.append(Ydata)
      else:
        dataXDfs.append(Xdata)
        dataYDfs.append(Ydata)



    # plt.rc('font', family='Times New Roman')

    # marker = ['.', 'x', '+', '.', 'x', '.', '.', '.', '.','.']
    # label = ['BVFP (z3)', 'BVFP (bitwuzla)', 'BVFP (mathsat5)', 'RSO (dreal)', 'RSO (cvc5)', 'ISC (z3)', 'FUZZ (jfs)', 'Search (gosat)', 'Synergy', 'smt-jfs']  # 标签序列参数
    # color = ['b', 'b', 'b', 'y', 'y', 'r', 'c', 'm', 'g', 'k']  # 颜色参数序列

    marker = ['.', 'x', '+', '.', 'x', '.', '.', '.', '.']
    label = ['BVFP (Z3)', 'BVFP (Bitwuzla)', 'BVFP (MathSAT5)', 'RSO (dReal)', 'RSO (CVC5)', 'ISC (Z3)', 'FUZZ (JFS)', 'Search (goSAT)', 'Synergy']  # 标签序列参数
    color = ['b', 'b', 'b', 'y', 'y', 'r', 'c', 'm', 'g']  # 颜色参数序列

    fig, ax = plt.subplots()
    f_line(ax, dataXBfs, dataYBfs, marker, label, color, cname)  # 调用函数
    # plt.show()

    plt.savefig("fig_branch_1/" + cname + "_bfs_covtrend_b.pdf", dpi=300, bbox_inches='tight', pad_inches=0.1)
    # plt.savefig("figyx/" + cname + "_bfs_covtrend.pdf", dpi=300, bbox_inches='tight', pad_inches=0.1)
    plt.close()

    # plt.rc('font', family='Times New Roman')

    # marker = ['.', 'x', '+', '.', 'x', '.', '.', '.', '.', '.']
    # label = ['BVFP (z3)', 'BVFP (bitwuzla)', 'BVFP (mathsat5)', 'RSO (dreal)', 'RSO (cvc5)', 'ISC (z3)', 'FUZZ (jfs)',
    #          'Search (gosat)', 'Synergy', 'smt-jfs']  # 标签序列参数
    # color = ['b', 'b', 'b', 'y', 'y', 'r', 'c', 'm', 'g', 'k']  # 颜色参数序列

    marker = ['.', 'x', '+', '.', 'x', '.', '.', '.', '.', '.']
    label = ['BVFP (Z3)', 'BVFP (Bitwuzla)', 'BVFP (MathSAT5)', 'RSO (dReal)', 'RSO (CVC5)', 'ISC (Z3)', 'FUZZ (JFS)', 'Search (goSAT)', 'Synergy']  # 标签序列参数
    color = ['b', 'b', 'b', 'y', 'y', 'r', 'c', 'm', 'g']  # 颜色参数序列

    fig, ax = plt.subplots()
    f_line(ax, dataXDfs, dataYDfs, marker, label, color, cname)  # 调用函数
    # plt.show()
    plt.savefig("fig_branch_1/" + cname + "_dfs_covtrend_b.pdf", dpi=300, bbox_inches='tight', pad_inches=0.1)
    # plt.savefig("figyx/" + cname + "_dfs_covtrend.pdf", dpi=300, bbox_inches='tight', pad_inches=0.1)
    plt.close()
