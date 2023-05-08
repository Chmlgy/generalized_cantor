theory IsarFive imports Main HOL.Fun
begin

lemma "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by (auto simp add: surj_def)
  thus "False" by blast
qed

lemma
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"
proof -
  from s have "\<exists>a. {x. x \<notin> f x} = f a" by (auto simp add: surj_def)
  thus "False" by blast
qed

lemma fixes a b :: int assumes "b dvd (a+b)" shows "b dvd a"
proof -
  have "\<exists> k'. a = b*k'" if asm: "a+b = b*k" for k
  proof
    show "a = b*(k-1)" using asm by(simp add: algebra_simps)
  qed
  then show ?thesis using assms by(auto simp add: dvd_def)
qed

(*Exercise 5.1*)

(*End of exercise*)

end
