# Class 4

## C06

### S03

#### 1. <>

instance : Zero GaussInt :=
  ⟨⟨0, 0⟩⟩

此处实际上希望利用lean4中名为Zero的class，因此我们需要证明高斯整数满足class的条件，也即高斯整数具有零元

两层<>的理解 : 内层的<0,0>定义了一个高斯整数，也即re = 0, im = 0; 外层的<>为instance的语法

instance : Zero GaussInt where
  zero := ⟨0, 0⟩

instance : Zero GaussInt where
  zero := {
    re := 0
    im := 0
  }

实际上只写一层尖括号lean4也可以接受

Zero(0), One(1), Neg(-), Add(+), Mul(*)等类的作用 : 方便对某个新定义的类使用对应的记号

#### 2. special notation

instance instCommRing : CommRing GaussInt where
  zero := 0
  one := 1
  add := (· + ·)
  neg x := -x
  mul := (· * ·)
  add_assoc := by
    intros
    ext <;> simp <;> ring

(· + ·) ： lambda表达式的特殊写法，等价于
fun x y -> x + y

zero := 0 : 实际上为一个结构定义了Zero类(零元)之后就可以省略该步骤，此处为了方便学习全部列出，其他符号同理

ext <;> simp <;> ring : <;>可以对多个目标使用同一个命令

#### 3. intros

相当于多次使用intro，会自动决定是否生成名称

#### 4. Nontrivial

非平凡的，即存在两个不相等的元素

#### 5. /

1/0 = 0
若b为正整数，a/b会进行下取整，否则a/b会上取整

#### 6. <|

Eq.symm <| Int.ediv_add_emod a b 等价于
Eq.symm $ Int.ediv_add_emod a b 等价于
Eq.symm (Int.ediv_add_emod a b)

#### 7. 欧几里得整环

在lean4中证明是欧几里得整环并不需要norm function单调递减的性质，只要求norm function是良序的，即辗转相除法能在有限步内结束
