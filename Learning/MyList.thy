theory MyList
imports Main
begin

declare [[names_short]] (*Only for this exercise so as to not see MyList.list. !*)
datatype 'a list = Nil | Cons 'a "'a list"

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app Nil ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev Nil = Nil" |
"rev (Cons x xs) = app (rev xs) (Cons x Nil)"

value "rev (Cons True (Cons False Nil))"

lemma app_Nil2 [simp]: "app xs Nil = xs"
  apply(induction xs)
  apply(auto)
  done

lemma app_assoc [simp]: "app (app xs ys) zs = app xs (app ys zs)"
  apply(induction xs)
  apply(auto)
  done

lemma rev_app [simp]: "rev (app xs ys) = app (rev ys) (rev xs)"
  apply(induction xs)
  apply(auto)
  done

theorem rev_rev [simp]: "rev (rev xs) = xs"
  apply(induction xs)
  apply(auto)
  done

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count x Nil = 0" |
"count x (Cons z zs) = (if x = z then 1 + count x zs else count x zs)"

value "count (3::int) (Cons 2 (Cons (-3) (Cons 2 (Cons 3 Nil))))"

fun length :: "'a list \<Rightarrow> nat" where
"length Nil = 0" |
"length (Cons x xs) = 1 + length xs"

theorem occurance_lte_length: "count x xs \<le> length xs"
  apply(induction xs)
  apply(auto)
  done

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc Nil x = Cons x Nil" |
"snoc (Cons z zs) x = Cons z (snoc zs x)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse Nil = Nil" |
"reverse (Cons x xs) = snoc (reverse xs) x"

lemma reverse_snoc [simp]: "reverse (snoc xs x) = Cons x (reverse xs)"
  apply(induction xs)
  apply(auto)
  done

theorem reverse_reverse: "reverse(reverse xs) = xs"
  apply(induction xs)
  apply(auto)
  done

fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0" |
"sum_upto x = x + sum_upto (x-1)"

theorem gauss_sum: "sum_upto x = (x * (x+1)) div 2"
  apply(induction x)
  apply(auto)
  done

end
