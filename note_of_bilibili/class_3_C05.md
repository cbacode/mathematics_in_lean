# Class 3

## C05

### S01

#### 1. rwa

先执行rw,再尝试运行assumption结束证明

#### 2. simpa

先执行simp,再尝试运行assumption结束证明
simpa [...] using e会同时对结论以及假设e进行简化，之后尝试结束证明

#### 3. 简写

Nat.gcd m n可以简写为m.gcd n

#### 4. 简单数字的互质

norm_num可以证明一些简单数字之间的互质，但是注意lean4在数学计算上劣于python等专用于计算的语言

#### 5. 多重推出建议使用逗号代替

A -> B -> C => A, B -> C

#### 6. 在多个命题中使用同一个证明命令

tac \<;\> tac' : 先运行tac将原目标分裂成多个新目标，对每个新目标都使用tac'

### S02

#### 1. |

| 可以视为花括号，表示分类讨论

#### 2. induction

induction 数学归纳法

用法：
induction' h with d hd

  1. 归纳假设 n=0
  2. P n -> P n+1

#### 3. sum

sum s f 对s中的元素求f x的和
注意有穷集和无穷集的加和在lean4中定义不同

#### 4. prod

prod s f 对s中的元素求f x的乘积

#### 5. range

range
x in range succ.n 表示1到n的集合（注意是左闭右开）

#### 6. 自然数

自然数定义：先定义0，再定义后继

加法定义：x+0=x，x+succ y=succ x+y

乘法定义：x\*0=0 x\*succ y=x\*y+x

### S03

#### 1. interval_cases

interval_cases n : 遍历在当前条件下变量n可以取得的所有值

interval_cases using ha hb : 显式指定变量的上下限

#### 2. revert

intro的反向操作，通过推出符号将假设转移到结论中

#### 3. decide

尝试通过单纯的逻辑运算简化结论，使得推理结果为True，若成功则完成证明

使用时必须先使用revert将结论中使用到的假设全部转移到结论中

#### 4. induction

第二数学归纳法
induction' n using Nat.strong_induction_on with n ih

#### 5. tauto

可以证明只跟与或非相关的命题，使用后必须结束证明

#### 6. erase

erase s a ： 从集合s中丢弃元素a
