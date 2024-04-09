from scipy.stats import ranksums

# 两组样本数据
group1 = [10, 12, 14, 16, 18]
group2 = [13, 15, 17, 19, 21]

# 执行Wilcoxon秩和检验
statistic, p_value = ranksums(group1, group2)

# 打印结果
print("Wilcoxon秩和检验统计量:", statistic)
print("p 值:", p_value)

# 解释结果
alpha = 0.05
if p_value < alpha:
    print("拒绝原假设，两组样本的中位数存在显著差异。")
else:
    print("接受原假设，两组样本的中位数没有显著差异。")
