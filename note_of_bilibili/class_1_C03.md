# Class 1

## C03

### S01

处理任意命题

#### 1. 任意

"\all"

若任意符号位于结论，证明方式为通过intro x引入一个变量x

若任意符号位于假设，利用方式为在假设之后添加命题的对象，e.g. apply h x表示将任意命题中的变量设为x

一行化证明：
fun x -> 定理 (定理需要的假设)
x代表引入的变量或假设(相当于intro x)
fun x -> _ : 可以查看当前需要证明的目标

#### 2. intro

intro除了可以引入新变量外，还可以拆解推出命题。拆解后结果为推出结果作为目标，推出条件作为条件。

#### 3. assumption

命题结论位于条件中

#### 4. dsimp

根据定义进行化简

### S02

处理存在命题

#### 1. use

use可以证明存在性命题。用use指定一个数，之后证明这个数符合条件
存在为"\\ex"

#### 2. norm_num

处理具体数字计算以及比大小相关的指令

#### 3. <,>

"\\<","\\>" : 左侧填入被指定的数字，右边填入证明过程。

若输入5/2出现问题可以尝试(5 : \R)/2，指定分子为实数避免被认为是正整数。

#### 4. rcases

rcases可以处理假设中有存在性的命题。

语法:
rcases 假设 with <变量名 新假设名>
注：此处尖括号为"\\<","\\>"

#### 5. rintro

rintro可以同时处理rcases和intro两种类型的指令

rintro "\\<" x, P "\\>"等价于
intro h
rcases h with "\\<" x, P "\\>"

常用于证明合取假设推出的命题。
如 A \\and B -> C

若在rintro中使用到 h1 | h2 类似的格式（在假设中出现or），则可能需要加括号

#### 6. 一行化证明

fun x -> 定理 (定理需要的假设)
x代表引入的变量或假设(相当于intro x)
fun x -> _ : 可以查看当前需要证明的目标

#### 7. obtain

与rcases用法类似

#### 8. cases

与rcases用法类似

### S03

处理否命题"\\not"

#### 1. intro

否命题等价于原命题推出false。

若否命题位于假设，则可以利用intro将原命题变为假设，目标变为推出false(得出矛盾)

可以通过非命题得出矛盾：
e.g. h : P, h' : \\not P
apply h' h 即可得到false

可以通过不等式得出矛盾：
e.g. h : a < b, h' : a > b
linarith 即可得到false

#### 2. have

若have命题未给定名称，则可以利用this指代最近的一个未指定名称的命题。

#### 3. by_contra

反证法，将结论的反命题变为条件，证明目标变为false。

#### 4. push_neg

将否定符号消除

#### 5. contrapose!

将命题变为逆否命题。

用法： contrapose! h
指定"\\not" h作为转换后的目标

#### 6. exfalso

条件出现false则命题得证。

使用exfalso会使证明目标变为false。

#### 7. absurd

在absurd命令后证明false即可使命题得证。
若h为假设之一，则absurd h会将结论变为证明\\not h

#### 8. contradiction

contradiction可以检测命题是否有矛盾。(在分类讨论中常用)
