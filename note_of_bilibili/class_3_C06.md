# Class 3

## C06

### S01

#### 1. structure

structure point where
  结构体元素名 : 结构体元素类型

structure中除了包含元素，还可以加入性质

structure中可以只包含性质

#### 2. ext

@[ext] 自动生成某些定理

by ext可以使用被自动生成的定理

#### 3. def

实例化结构体
def 实例名称：结构体名称 where
  结构体元素名 := ...
给元素赋值
赋值过程会进行自动的类型转换

def 实例名称：结构体名称 := <结构体元素值，结构体元素值，...>

以上两种方式实际上调用了 结构体名称.mk（make） 函数

#### 4. 修改mk函数的名称

structure point where build ::
  结构体元素名 : 结构体元素类型

#### 5. 函数

def 函数名称 （函数输入）：结构体名称 where
  结构体元素名 := ...
给元素赋值
赋值过程会进行自动的类型转换

def 函数名称（函数输入）：结构体名称 := <结构体元素值，结构体元素值，...>

#### 6. 函数空间

namespace 函数空间名 可以创建一个函数空间。

open 函数空间名 可以打开一个函数空间。

end 函数空间名 可以关闭一个函数空间。

在namespace 函数空间名 中定义的函数，在函数空间外必须指定函数空间名才能使用

#### 7. 使用函数

结构体实例名1.结构体函数名 结构体实例名2 （语法糖）
等价于
函数空间名.结构体函数名 结构体实例名1 结构体实例名2

#### 8. protected

protected theorem：即使open了一个函数空间，我们依然需要指定前缀才可以使用这个定理

#### 9. dsimp

dsimp的能力弱于simp，只能使用逻辑恒等变形，不能使用lean4库中的定理

#### 10. repeat'

repeat' t : 若在执行t的过程中出现了多个目标，则对每个目标执行repeat t

#### 11. field_simp

field_simp比ring智能，它可以解决跟除法相关的命题

#### 12. trans

trans：利用传递性证明定理。
e.g. 欲证a=b先证a=c且b=c

#### 13. subtype

subtype：变量定义//变量性质

lean4会记住定义的顺序，因此在structure中可以使用.1或.fst等指定需要使用的定义或定理

#### 14. sorry

在定义时使用 def a := sorry之后，可以点击旁边的小灯泡，此时lean4会自动帮你生成定义需要的骨架

#### 15. norm_num 与 field_simp

ring与norm_num都无法处理与除法相关的问题，field_simp可以处理

#### 16. Fin

有限集，Fin n表示0 ~ n-1的所有自然数

### S02

#### 1. 群范畴

群范畴包括一个集合以及集合上的群结构

#### 2. 等价关系

等价关系包含两个集合\alpha与\beta，从\alpha到\beta的映射以及从\beta到\alpha的映射，并且满足两个映射互逆

Equiv \alpha \beta表示\alpha到\beta之间的所有等价关系

#### 3. trans

当f与g均为映射时，f.trans g表示f与g的复合，即g \o f

#### 4. Perm

Equiv.Perm表示\alpha到\alpha的等价关系

PermGroup表示\alpha到\alpha之间的所有置换构成的群

Equiv.refl表示到自己的id映射，是一个具体映射

#### 5. AddGroup

加法群，实际上与乘法群只在定理名称上有区别

#### 6. class

class与structure的唯一区别在class可以定义instance，instance可以用于自动推理，用户不需要使用名字来调用instance对应的定义

#### 7. inhabited

inhabited：集合中至少有一个元素
