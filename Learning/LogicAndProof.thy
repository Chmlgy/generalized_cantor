theory LogicAndProof imports Main TypesAndFunctions
begin

(*Exercise 4.1*)
fun set :: "'a tree \<Rightarrow> 'a set" where
"set Tip = {}" |
"set (Node l x r) = (set l) Un {x} Un (set r)"

value "set (Node (Node Tip (3::nat) Tip) 5 (Node (Node (Tip) 10 (Node (Tip) 2 (Tip))) 7 (Tip)))"

fun ord :: "int tree \<Rightarrow> bool" where
"ord Tip = True" |
"ord (Node Tip x Tip) = True" |
"ord (Node Tip x (Node l2 x2 r2)) = (if x > x2 then False else ord (Node l2 x2 r2))" |
"ord (Node (Node l2 x2 r2) x r) = (if x2 \<ge> x then False else ord (Node l2 x2 r2) \<and> ord r)"

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
"ins x Tip = Node Tip x Tip" |
"ins x (Node l y r) = (if x > y then Node l y (ins x r) else
                      (if x = y then Node l y r else Node (ins x l) y r))"

theorem set_ins [simp]: "set (ins x t) = {x} \<union> set t"
  apply(induction t)
  apply(auto)
  done

theorem ord_ins [simp]: "ord t \<Longrightarrow> ord (ins i t)"
  apply(induction t rule: ord.induct)
  apply(auto)
  done
(*End of exercise*)

thm ord_ins[of "Tip" "5"]
thm conjI[OF refl[of "a"] refl[of "b"]]

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x" |
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply(induction rule: star.induct)
  apply(assumption)
  apply(metis step)
  done

(*Exercises 4.2-7*)
inductive palindrome :: "'a list \<Rightarrow> bool" where
empty: "palindrome []" |
single: "palindrome [a]" |
pal_append: "palindrome xs \<Longrightarrow> palindrome (a # xs @ [a])"

lemma "palindrome xs \<Longrightarrow> rev xs = xs"
  apply(induction rule: palindrome.induct)
  apply(simp)
  apply(simp)
  apply(simp)
  done

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl': "star' r x x" |
step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

lemma "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"
  apply(induction rule: star.induct)
  apply(auto intro: step refl)
  done

(*TODO: theorem "star' r x y \<Longrightarrow> star r x y"*)
(*End of exercises*)

end
