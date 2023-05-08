theory TypesAndFunctions
imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l x r) = Node (mirror r) x (mirror l)"

lemma [simp]: "mirror (mirror t) = t"
  apply(induction t)
  apply(auto)
  done

fun lookup :: "('a * 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option" where
"lookup Nil x = None" |
"lookup ((x, y) # xs) z = (if x = z then Some y else lookup xs z)"

fun div2 :: "nat \<Rightarrow> nat" where
"div2 0 = 0" |
"div2 (Suc 0) = 0" |
"div2 (Suc (Suc n)) = Suc (div2 n)"

lemma "div2 n = n div 2"
  apply(induction n rule: div2.induct)
  apply(auto)
  done

(*Exercises 2.6, 2.7, and 2.8*)
fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []" |
"contents (Node l x r) = x # (contents l @ contents r)"

value "contents (Node (Node Tip (3::nat) Tip) 5 (Node (Node (Tip) 10 (Node (Tip) 2 (Tip))) 7 (Tip)))"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0" |
"sum_tree (Node l x r) = sum_tree l + x + sum_tree r"

theorem sum_content: "sum_tree t = sum_list (contents t)"
  apply(induction t)
  apply(auto)
  done

fun pre_order :: "'a tree \<Rightarrow> 'a list" where
"pre_order Tip = []" |
"pre_order (Node l x r) = (x # []) @ pre_order l @ pre_order r"

fun post_order :: "'a tree \<Rightarrow> 'a list" where
"post_order Tip = []" |
"post_order (Node l x r) = post_order l @ post_order r @ (x # [])"

value "post_order (Node (Node Tip (3::nat) Tip) 5 (Node (Node (Tip) 10 (Node (Tip) 2 (Tip))) 7 (Tip)))"

lemma "pre_order (mirror t) = rev (post_order t)"
  apply(induction t)
  apply(auto)
  done

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse x [] = x # []" |
"intersperse x (y # []) = y # []" |
"intersperse x (y # ys) = y # x # (intersperse x ys)"

value "intersperse (3::nat) [1,2,4,9,0]"

lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply(induction xs rule: intersperse.induct)
  apply(auto)
  done
(*End of exercises*)

(*Exercise 2.9*)
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc (add m n)"

lemma add_Suc [simp]: "add m (Suc n) = Suc (add m n)"
  apply(induction m)
  apply(auto)
  done

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"

lemma "itadd m n = add m n"
  apply(induction m arbitrary: n)
  apply(auto)
  done
(*End of exercise*)

(*Exercise 2.10
datatype tree0 = Leaf | Node "tree0" "tree0"

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Leaf = 1" |
"nodes (Node l r) = nodes l + 1 + nodes r"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

theorem nodes_explode: "nodes (explode n t) = 2^n * (nodes t + 1) - 1"
  apply(induction n arbitrary: t)
  apply(auto simp add: algebra_simps)
  done
End of exercise*)

(*Exercise 2.11*)
datatype exp = Var | Const "int" | Add "exp" "exp" | Mul "exp" "exp"

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x" |
"eval (Const c) x = c" |
"eval (Add e1 e2) x = eval e1 x + eval e2 x" |
"eval (Mul e1 e2) x = eval e1 x * eval e2 x"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] x = 0" |
"evalp (c # cs) x = c + x * (evalp cs x)"

fun add_list :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"add_list xs [] = xs" |
"add_list [] xs = xs" |
"add_list (x # xs) (y # ys) = (x + y) # add_list xs ys"

fun scale_list :: "int \<Rightarrow> int list \<Rightarrow> int list" where
"scale_list x [] = []" |
"scale_list x (y # ys) = (x * y) # scale_list x ys"

fun mul_list :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"mul_list _ [] = []" |
"mul_list [] _ = []" |
"mul_list (x # xs) ys = add_list (scale_list x ys) (0 # mul_list xs ys) "

value "mul_list [1, 1, 1, 1] [1, 1, 1, 2]"

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs Var = [0, 1]" |
"coeffs (Const c) = [c]" |
"coeffs (Add e1 e2) = add_list (coeffs e1) (coeffs e2)" |
"coeffs (Mul e1 e2) = mul_list (coeffs e1) (coeffs e2)"

lemma evalp_sum [simp]: "evalp (add_list e1 e2) x = evalp e1 x + evalp e2 x"
  apply(induction e1 e2 arbitrary: x rule: add_list.induct)
  apply(auto simp add: algebra_simps)
  done

lemma evalp_preserves_scaling [simp]: "evalp (scale_list c xs) a = c * evalp xs a"
  apply(induction xs)
  apply(auto simp add: algebra_simps)
  done

lemma evalp_mul [simp]: "evalp (mul_list e1 e2) x = evalp e1 x * evalp e2 x"
  apply(induction e1 e2 arbitrary: x rule: mul_list.induct)
  apply(auto simp add: algebra_simps)
  done

theorem evalp_eval_correspondence: "evalp (coeffs e) x = eval e x"
  apply(induction e)
  apply(auto)
  done
(*End of exercise*)

end
