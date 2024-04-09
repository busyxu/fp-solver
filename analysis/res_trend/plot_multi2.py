import numpy as np
import matplotlib.pyplot as plt
from scipy.interpolate import interp1d

# 示例数据
x_data = [np.linspace(0, 10, np.random.randint(10, 20)) for _ in range(5)]  # 生成5组随机的 x 数据
y_data = [np.sin(x) + np.random.normal(0, 0.1, len(x)) for x in x_data]  # 生成5组随机的 y 数据

# 对每组数据进行插值并绘制曲线
for i in range(len(x_data)):
    x = x_data[i]
    y = y_data[i]

    # 对数据进行插值
    f = interp1d(x, y, kind='linear')

    # 创建相同长度的 x 值
    x_new = np.linspace(min(x), max(x), 100)

    # 计算插值后的 y 值
    y_new = f(x_new)

    # 绘制插值后的曲线
    plt.plot(x_new, y_new, label=f'Data {i + 1} (Interpolated)')

    # 添加阴影
    plt.fill_between(x_new, y_new, alpha=0.2)  # alpha 参数控制阴影的透明度

# 添加图例和标签
plt.legend()
plt.xlabel('X')
plt.ylabel('Y')
plt.title('Interpolated Data with Shadow')

# 显示图形
plt.show()
