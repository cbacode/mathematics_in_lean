# Class 4

## C07

### S01

#### 1. One

class One₁ (α : Type) where
  /-- The element one -/
  one : α

在α中取一个元素，设置其为单位元

\#check One₁.one -- One₁.one {α : Type} [self : One₁ α] : α

{α : Type} : 隐式调用α，希望lean4通过上下文推断应当填充给α的内容，若无法推断则报错，如下 :

typeclass instance problem is stuck, it is often due to metavariables
  One₁ ?m.1603

[self : One₁ α] : 希望lean4自行推断α上具有One₁对应的instance，并且读出对应的元素

#### 2. @[class]

@[class] structure One₂ (α : Type) where
  /-- The element one -/
  one : α

@[class]可以产生与class类似的效果，但是

\#check One₂.one -- One₂.one {α : Type} (self : One₂ α) : α

(self : One₂ α) : 希望由用户提供相应的信息
@One₂.one : 显式指定One₂.one的所有参数

#### 3. 罗马字母1

\b1

#### 4. 菱形

\diamond

#### 5. notation

@[inherit_doc]
notation "𝟙" => One₁.one

用一个记号来表示One₁.one

@[inherit_doc] : 在相同的文件中寻找定义

#### 6. infixl

e.g. infixl:70 " ⋄ "   => Dia₁.dia

infixl代表该符号所在的表达式满足左结合，infixr代表该符号所在的表达式满足右结合，postfix代表后缀

infixl:70 70代表结合强度，先算结合强度大的符号
postfix:Max 结合强度最大

#### 7. Simigroup

半群

#### 8. attribute

attribute [instance] Semigroup₁.toDia₁

允许接收一个Semigroup₁并且自动推断toDia₁的类型

attribute [simp]

向simp中添加一个定理

#### 9. extends

继承某个类，会自动制造参数并且自动注册该参数

#### 10. trace.Meta.synthInstance

set_option trace.Meta.synthInstance true in
  example {α : Type} [DiaOneClass₁ α] (a b : α) : Prop := a ⋄ b = 𝟙

要求lean输出进行Instance推理的过程

#### 11. Monoid

含幺半群

#### 12. extends

class Monoid₁ (α : Type) extends Semigroup₁ α, DiaOneClass₁ α

若同时extends多个class，则同一个符号对应相同的内涵

class Monoid₂ (α : Type) where
  toSemigroup₁ : Semigroup₁ α
  toDiaOneClass₁ : DiaOneClass₁ α

此时会得到两个完全不相干的Diamond运算

#### 13. export

将某些定理名称送到root namespace中，可以实现不指定类名使用部分函数

#### 14. @[to_additive]

环中同时出现加法与乘法，我们希望使用不同的符号表示加法与乘法，但是加法与乘法满足某些共同的性质，我们不希望多次证明类似的定理

@[to_additive AddSemigroup₃]表示证明乘法版本的定理，lean会自动生成加法版本的定理，名称符合规范时lean4可以生成对应的定理名称

@[to_additive (attr := simp)]会将生成的两个定理一同加入simp

#### 15. whatsnew in

展示产生的新定理

### S02

定义代数结构之间的映射

#### 1. coe

上箭头为coe的缩写，可以完成类似自然数嵌入到整数中的任务

SetCoe.ext 在子集中相等的元素在原集合中也相等

#### 2. MonoidHomCLass

class MonoidHomClass₁ (F : Type) (M N : Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

定义含幺半群同态构成的集簇，可以使得在环中证明环同态后，可以自动化连接乘法含幺半群同态和加法含幺半群同态相关的定理

#### 3. outParam

在进行类型推理时，带outParam的参数后被推出，但不会改变对应的数学含义

### S03 子对象

#### 1. Set

lean中的集合与集合论中的集合不相同

lean4中的子集为集合打到定理的一个映射，表示集合中取值为真的元素位于集合内，取值为假的元素位于集合外

#### 2. subType

我们无法从带有性质的集合中取出元素，因此在定义(x : N)的过程中进行了一次强制类型转换，变为了(x : N.carrier)

在子集N中取一个元素x实际上是定义元素x属于一个Subtype，subType的property性质会保留x在子集N中这个信息

#### 3. Inf

由于子群的交依然为子群，子群天然具有latties结构，因此我们可以取下界

#### 4. 等价关系

Setoid : 集合上的等价关系
quotient s a : 返回\alpha商s中，a所在的等价类
\\/(\\quot) : 商

TODO : 重听1：00：00之后的部分