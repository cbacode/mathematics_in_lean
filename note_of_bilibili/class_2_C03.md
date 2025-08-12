# Class 2

## C03

### S04 A and B

#### 1. constructor

证明A \\and B类型的命题。

会将命题拆分为两个目标，分别为A和B。

A \\and B := by
  constructor
  \\. A的证明
  \\. B的证明

"\\."可以省略。

一行化证明：
A \\and B := \\< A的证明 , B的证明 \\>

#### 2. left, right

若A \\and B类型的命题位于条件h，可以通过h.left来指定A，通过h.right来指定B。

若A \\and B类型的命题位于条件h，h.2代表right h.1代表left

#### 3. next

略

#### 4. match

略

#### 5. \\< \\>

尖括号中可以有两个以上的命题，lean4会进行自动组合

constructor \\<;\\> 命题名称
在尖括号中每个位置都写入该命题名称

#### 6. iff

p iff q ：\\< p -> q ，q -> p \\>

不被定义为 p -> q \\and q -> p ，但具有类似的行为。

在假设中出现\\iff：利用h.mp使用正向命题，利用h.mpr利用反向命题

在结论中出现\\iff：利用constructor或者\\<,\\> 将结论拆开

### S05 A or B

#### 1. A or B

A or B命题位于结论时：用left或right指定要证明的一侧

一行化证明：
Or.inl表示证明左侧
Or.inr表示证明右侧

A or B命题位于假设时：rcases h with A | B

该命令会将指令分解为两个结论相同的命题，第一个命题用A作为条件，第二个命题用B作为条件

注意与"\\<","\\>"进行区分

#### 2. \\not

对于任意命题，P 或\not P恒正确
cases em P会利用以上定理进行分类讨论
by_cases可以为分类讨论的命题对象命名

### S06

#### 1. ext

ext用于证明函数相等，该命令会向函数中插入自变量，使得我们可以证明对于任意的自变量x，f x=g x
通过代入数值，将抽象的映射相等转变为数字相等

#### 2. congr

congr用于通过证明x = y来证f x=f y

#### 3. convert

略

#### 4. unfold

unfold打开定义，打开定义对编译没有影响。

#### 5. specialize

specialize可以将定义中的任意命题填入具体数值。
