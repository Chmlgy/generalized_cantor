section \<open>Generalized Cantor's Theorem and Instances\<close>

theory GeneralCantor imports
  Complex_Main
  "HOL-Library.Countable"
  "HOL-Analysis.Analysis"
  "HOL-ZF.HOLZF"
  "Universal_Turing_Machine.Turing_aux"
  "Universal_Turing_Machine.TuringDecidable"
  "Universal_Turing_Machine.HaltingProblems_K_aux"
  "Universal_Turing_Machine.TuringComputable"
  "Universal_Turing_Machine.DitherTM"
  "Universal_Turing_Machine.CopyTM"
begin

text \<open>
  1. The most abstracted version of Cantor's theorem.
  S x T ---- f ----> Y
    ^                |
    |                |
(beta, Id)         alpha             S ---- beta_comp ----> T              beta \<circ> beta_comp = Id
    |                |
    |                v
    T   ---- g ----> Y
\<close>
theorem "Abstracted_Cantor":
  fixes f :: "'b \<Rightarrow> 'a \<Rightarrow> 'c" and \<alpha> :: "'c \<Rightarrow> 'c" and \<beta> :: "'a \<Rightarrow> 'b" and \<beta>_c :: "'b \<Rightarrow> 'a"
  assumes surjectivity: "surj f"
  and no_fixed_point: "\<forall>y. \<alpha> y \<noteq> y"
  and right_inverse: "\<forall>s. \<beta> (\<beta>_c s) = s"
  shows "False"
proof -
  from surjectivity have "\<forall>h :: 'a \<Rightarrow> 'c. \<exists>t. h = f t" by auto
  hence "\<exists>t. (\<alpha> \<circ> (\<lambda>t'. f (\<beta> t') t')) = f t" by simp
  then obtain t0 where "(\<alpha> \<circ> (\<lambda>t'. f (\<beta> t') t')) = f t0" ..
  hence "(\<alpha> \<circ> (\<lambda>t'. f (\<beta> t') t')) (\<beta>_c t0) = f t0 (\<beta>_c t0)" by (rule arg_cong)
  hence "\<alpha> (f t0 (\<beta>_c t0)) = f t0 (\<beta>_c t0)" using right_inverse by simp
  thus "False" using no_fixed_point by simp
qed


text \<open>
  2. An instance of the above theorem, where S = T and \<beta> = Id. Still a quite general version
  of Cantor's theorem.
  T x T ---- f ----> Y
    ^                |
    |                |
 Diagonal          alpha
    |                |
    |                v
    T   ---- g ----> Y
\<close>
theorem "Generalized_Cantor":
  fixes alpha :: "'b \<Rightarrow> 'b" and f :: "'a \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes surjectivity: "surj f"
  and no_fixed_point: "\<forall>y. alpha y \<noteq> y"
  shows "False"
  apply(rule Abstracted_Cantor[of f alpha "\<lambda>x. x" "\<lambda>x. x"])
  apply(auto simp add: no_fixed_point surjectivity)
  done


text \<open>
  3. An instance of the above version of Cantor's theorem, where 'b = bool and \<alpha> = \<not>.
  Entailing the fact that no surjective functions exists from a set to its power set.
  T ---- f ----> \<P>(T)
\<close>
theorem "Classic_Cantor":
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes surjectivity: "surj f"
  shows "False"
  apply(rule Generalized_Cantor[of f Not])
  apply(auto simp add: surjectivity)
  done


text \<open>
  4. An instance of the above theorem. With the set 'a being natural numbers.
 |\<P>(\<nat>)| > |\<nat>|
\<close>
theorem "Classic_Nat_Cantor":
  fixes f :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  assumes surjectivity: "surj f"
  shows "False"
  apply(rule Classic_Cantor[of f])
  apply(simp add: surjectivity)
  done


text \<open>
  5. Contrapositive of Cantor's Theorem:
  If Y is a set and there exists a set T together with a function f: T x T \<longrightarrow> Y
  such that all functions g: T \<longrightarrow> Y are representable by f, i.e. there exists
  a t in T such that g = f t, then all functions \<alpha>: Y \<longrightarrow> Y admits a fixed point.
\<close>
theorem "Contrapositive_Cantor":
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes surjectivity: "surj f"
  shows "\<forall>\<alpha> :: 'b \<Rightarrow> 'b. \<exists>y. \<alpha> y = y"
  by (meson Generalized_Cantor surjectivity)


text \<open> 
  6. All endomorphisms admitting a fixed point means the set has only one element.
  Still, we will keep the definition of fixed points and do not make assumptions on the cardinality
  of Y. The reason being that fixed points easily generalize to categories unlike cardinality.
\<close>
lemma one_elem_to_fixed: "(\<forall>a b :: 'b. a = b) \<longrightarrow> (\<forall>\<alpha> :: 'b \<Rightarrow> 'b. \<exists>y. \<alpha> y = y)"
  by simp

lemma fixed_to_one_elem: "(\<forall>\<alpha> :: 'b \<Rightarrow> 'b. \<exists>y. \<alpha> y = y) \<longrightarrow> (\<forall>a b :: 'b. a = b)"
proof (rule ccontr)
  assume "\<not> ((\<forall>\<alpha> :: 'b \<Rightarrow> 'b. \<exists>y. \<alpha> y = y) \<longrightarrow> (\<forall>a b :: 'b. a = b))"
  hence contra: "(\<forall>\<alpha> :: 'b \<Rightarrow> 'b. \<exists>y. \<alpha> y = y) \<and> (\<exists>a b :: 'b. a \<noteq> b)" by simp
  from contra have fixed_point: "\<forall>\<alpha> :: 'b \<Rightarrow> 'b. \<exists>y. \<alpha> y = y" by simp
  from contra have diff_elem: "\<exists>a b :: 'b. a \<noteq> b" by simp
  then obtain a b where "a \<noteq> (b :: 'b)" by blast
  hence "\<exists> f :: 'b \<Rightarrow> 'b. f = (\<lambda>x. (if x = a then b else a))" by fast
  then obtain f where no_fixed_point: "\<forall>y :: 'b. f y \<noteq> y" by (metis \<open>a \<noteq> (b::'b)\<close>)
  thus "False" using fixed_point no_fixed_point by blast
qed

theorem "(\<forall>\<alpha> :: 'b \<Rightarrow> 'b. \<exists>y. \<alpha> y = y) \<longleftrightarrow> (\<forall>a b :: 'b. a = b)"
  by (metis fixed_to_one_elem)

text \<open>
 7. |\<real>| = |\<P>(\<nat>)|
\<close>

text \<open>
  7.1 Show that \<exists>f s.t. f: \<real> \<longlongrightarrow> \<P>(\<rat>) and f is injective. ==> |\<real>| \<le> 2^(\<aleph>_0)
\<close>
definition cut_set :: "real \<Rightarrow> (rat \<Rightarrow> bool)" where
"cut_set r = (\<lambda>q. of_rat q < r)"

lemma "contra_inj_cut_set": "\<forall>x y :: real. x \<noteq> y \<longrightarrow> cut_set x \<noteq> cut_set y"
  by (metis cut_set_def linorder_less_linear of_rat_dense order_less_not_sym)

lemma "inj_example_cut_set": "inj cut_set"
  by (meson contra_inj_cut_set injI)

lemma "\<exists>f :: real \<Rightarrow> (rat \<Rightarrow> bool). inj f"
  by (meson inj_example_cut_set)


text \<open>
  7.2 Show that \<exists>f s.t. f: (nat => bool) => real and f is surjective on [0, 1].
       \<Longrightarrow> 2^(\<aleph>_0) \<ge> |[0,1]|
\<close>
(*A function that is surjective on real numbers between 0 and 1: *)
definition seq_to_real :: "(nat \<Rightarrow> bool) \<Rightarrow> real" where
"seq_to_real f = \<Sum>{1/(2^n) | n. f n = True}"

(*Helper definition and functions to prove that the above function is surjective: *)
(*A function that returns the most significant binary digit for a real number between 0 and 1: *)
definition most_sig_bdig :: "real \<Rightarrow> nat" where
"most_sig_bdig x = Min {n. 1/(2^n) < x}" 

definition bool_mult :: "bool \<Rightarrow> real \<Rightarrow> real" where
"bool_mult b x = (if b = False then 0 else x)"

(*A function that expands a real number between 0 and 1 to its binary representation: *)
definition binary_remainder :: "(real \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real set" where
"binary_remainder bs x n = {bool_mult (bs x k)  1/(2^k) | k. 1 < k \<and> k < n}"

lemma [fundef_cong]:
  assumes "x = x'" and "n = n'" and "\<And>k. k < n \<Longrightarrow> bs x k = bs' x k"
  shows "binary_remainder bs x n = binary_remainder bs' x' n'"
  using assms unfolding binary_remainder_def
  by force

fun binary_sequence :: "real \<Rightarrow> nat \<Rightarrow> bool" where
"binary_sequence x 0 = (if most_sig_bdig x > 1 then False else True)" |
binseq_rem: "binary_sequence x (Suc n) =
  (if most_sig_bdig (x - \<Sum>(binary_remainder binary_sequence x n)) > Suc n
   then False else True)"

lemma binseq_no_rem: "binary_sequence x (Suc n) =
  (if most_sig_bdig (x - \<Sum>{bool_mult (binary_sequence x k)  1/(2^k) | k. 1 < k \<and> k < n}) > Suc n
   then False else True)"
  apply(simp add: binary_remainder_def)
  done

declare binseq_rem [simp del]
declare binseq_no_rem [simp add]

(* TODO:
lemma "\<forall>r :: real. 0 < r \<and> r < 1 \<longrightarrow> (\<exists>f :: nat \<Rightarrow> bool. seq_to_real f = r)"
*)


text \<open>
  7.3 Show that \<exists>f s.t. f: (0, 1) => real and f is surjective. f x = tan(\<pi>x - \<pi>/2).
      \<Longrightarrow> |(0, 1)| \<le> |\<real>|
\<close>
definition fitted_tan :: "real \<Rightarrow> real" where
"fitted_tan x = tan (pi*x - pi/2)"

definition fitted_arctan :: "real \<Rightarrow> real" where
"fitted_arctan x = (arctan x + pi/2) / pi"

lemma fitted_arctan: "0 < fitted_arctan y \<and> fitted_arctan y < 1 \<and> fitted_tan (fitted_arctan y) = y"
  unfolding fitted_arctan_def fitted_tan_def
  by (smt (verit) arctan divide_less_eq_1_pos divide_pos_pos field_sum_of_halves
      nonzero_mult_div_cancel_left times_divide_eq_right)

lemma fitted_reverse [simp]: "\<forall>y. fitted_tan (fitted_arctan y) = y"
  unfolding fitted_arctan_def fitted_tan_def
  by (simp add: arctan)

lemma fitted_surj [simp]: "\<forall>r. \<exists>x. fitted_tan x = r"
  using fitted_reverse by blast
  
lemma "fitted_tan ` {r. 0 < r \<and> r < 1} = UNIV"
  using fitted_arctan fitted_surj image_iff by fastforce


text \<open>
  8. Russel's Paradox
\<close>
(*
  In the context of Generalized_Cantor g becomes the characteristic function of sets that are not
  members of themselves, i.e. g x = True iff Not (Elem x x).
  
  So, if there was a set R which included all the sets that are not members of themselves then,
  Elem R = g
  
  But such R cannot exist as Elem is not surjective, it cannot represent g, by Classic_Cantor.
*)
lemma "Russels's_Paradox": "surj Elem \<Longrightarrow> False"
  apply (rule Classic_Cantor)
  by simp


text \<open>
  9. Counting argument to show the existence of non-r.e. languages
\<close>
instance action :: countable
  by countable_datatype

instance cell :: countable
  by countable_datatype

lemma "from_nat (to_nat (p::tprog0)) = p"
  by simp

definition "tprog0_accepts_num p n \<equiv> \<lbrace>\<lambda>tap. tap = ([], <n::nat>)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <1::nat> @ Bk \<up> l)\<rbrace>"

theorem "Non-re_Languages":
  assumes surjectivity: "surj tprog0_accepts_num"
  shows "False"
  apply(rule Abstracted_Cantor[of tprog0_accepts_num Not from_nat to_nat])
  apply(auto simp add: surjectivity)
  done


text \<open>
  10. Turing Machines and the Halting Problem
\<close>
lemma top_holds_for [intro, simp]: "top holds_for conf"
  apply (cases conf)
  by simp

definition "halts p ns \<equiv> \<exists>Q. \<lbrace>\<lambda>tap. tap = ([], <ns::nat>)\<rbrace> p \<lbrace>Q\<rbrace>"

lemma halts_alt_def: "halts p ns = (\<exists>n. is_final (steps0 (1, [], <ns>) p n))"
  unfolding halts_def Hoare_halt_def
  by force

lemma not_halts: "\<not> halts p ns \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <ns::nat>)\<rbrace> p \<up>"
  using Hoare_unhaltI halts_alt_def
  by presburger

lemma not_halts_alt: "\<not> halts p ns \<longrightarrow> (\<nexists>n. is_final (steps0 (1, [], <ns>) p n))"
  using halts_def Hoare_halt_def
  by blast

definition "decides_halting H \<equiv> \<forall>(p::tprog0) (ns::nat).
  \<lbrace>\<lambda>tap. tap = ([Bk], <(tm_to_nat p, ns)>)\<rbrace>
   H
  \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <(if halts p ns then 0::nat else 1::nat)> @ Bk \<up> l)\<rbrace>"

(*------------------------------TODO: AFP entry should include this.------------------------------*)
lemma Hoare_halt_tm_impl_Hoare_halt_mk_composable0_cell_list_aux: "\<lbrace>\<lambda>tap. tap = (cl', cl)\<rbrace> tm \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>tap. tap = (cl', cl)\<rbrace> mk_composable0 tm \<lbrace>Q\<rbrace>" 
  unfolding Hoare_halt_def
proof -
  assume A: "\<forall>tap. (tap = (cl', cl)) \<longrightarrow> (\<exists>n. is_final (steps0 (1, tap) tm n) \<and> Q holds_for steps0 (1, tap) tm n)"
  show "\<forall>tap. (tap = (cl', cl)) \<longrightarrow> (\<exists>n. is_final (steps0 (1, tap) (mk_composable0 tm) n) \<and> Q holds_for steps0 (1, tap) (mk_composable0 tm) n)"
  proof
    fix tap
    show "(tap = (cl', cl)) \<longrightarrow> (\<exists>n. is_final (steps0 (1, tap) (mk_composable0 tm) n) \<and> Q holds_for steps0 (1, tap) (mk_composable0 tm) n)"
    proof
      assume "tap = (cl', cl)"
      with A have "(\<exists>n. is_final (steps0 (1, tap) tm n) \<and> Q holds_for steps0 (1, tap) tm n)"
        by auto
      then obtain n where w_n: "is_final (steps0 (1, tap) tm n) \<and> Q holds_for steps0 (1, tap) tm n"
        by blast

      with \<open>tap = (cl', cl)\<close> have w_n': "is_final (steps0 (1, cl', cl) tm n) \<and> Q holds_for steps0 (1, cl', cl) tm n" by auto

      have "\<exists>n. is_final (steps0 (1, cl', cl) (mk_composable0 tm) n) \<and> Q holds_for steps0 (1, cl', cl) (mk_composable0 tm) n"

      proof (cases "\<forall>stp. steps0 (1,cl',cl) (mk_composable0 tm) stp = steps0 (1,cl', cl) tm stp")
        case True
        with w_n' have "is_final (steps0 (1, cl', cl) (mk_composable0 tm) n) \<and> Q holds_for steps0 (1, cl', cl) (mk_composable0 tm) n" by auto
        then show ?thesis by auto
      next
        case False
        then have "\<exists>stp. steps0 (1, cl', cl) (mk_composable0 tm) stp \<noteq> steps0 (1, cl', cl) tm stp" by blast
        then obtain stp where w_stp: "steps0 (1, cl', cl) (mk_composable0 tm) stp \<noteq> steps0 (1, cl', cl) tm stp" by blast

        show "\<exists>m. is_final (steps0 (1, cl', cl) (mk_composable0 tm) m) \<and> Q holds_for steps0 (1, cl', cl) (mk_composable0 tm) m"
        proof -
          from w_stp have F0: "0 < stp \<and>
                           (\<exists>fl fr.
                                   snd (steps0 (1, cl', cl) tm stp) = (fl, fr) \<and>
                                   (\<forall>i < stp. steps0 (1, cl', cl) (mk_composable0 tm) i = steps0 (1, cl', cl) tm i) \<and>
                                   (\<forall>j > stp. steps0 (1, cl', cl) tm (j) = (0, fl, fr) \<and> 
                                              steps0 (1, cl', cl) (mk_composable0 tm) j =(0, fl, fr)))"
            by (rule mk_composable0_tm_at_most_one_diff')

          from F0 have "0 < stp" by auto

          from F0 obtain fl fr where w_fl_fr: "snd (steps0 (1, cl', cl) tm stp) = (fl, fr) \<and>
                                   (\<forall>i < stp. steps0 (1, cl', cl) (mk_composable0 tm) i = steps0 (1, cl', cl) tm i) \<and>
                                   (\<forall>j > stp. steps0 (1, cl', cl) tm (j) = (0, fl, fr) \<and> 
                                              steps0 (1, cl', cl) (mk_composable0 tm) j =(0, fl, fr))" by blast


          have "steps0 (1, cl', cl) tm (stp+1) = steps0 (1, cl', cl) tm  n"
          proof (cases "steps0 (1, cl', cl) tm n")
            case (fields fsn fln frn)
            then have "steps0 (1, cl', cl) tm n = (fsn, fln, frn)" .
            with w_n' have "is_final (fsn, fln, frn)" by auto
            with is_final_eq have "fsn=0" by auto
            with \<open>steps0 (1, cl', cl) tm n = (fsn, fln, frn)\<close>  have "steps0 (1, cl', cl) tm n = (0, fln, frn)" by auto

            show "steps0 (1, cl', cl) tm (stp + 1) = steps0 (1, cl', cl) tm n"
            proof (cases "n \<le> stp+1")
              case True
              then have "n \<le> stp + 1" .
              show ?thesis
              proof -
                from \<open>steps0 (1, cl', cl) tm n = (0, fln, frn)\<close> and \<open>n \<le> stp + 1\<close> have "steps0 (1, cl', cl) tm (stp+1) = (0, fln, frn)"
                  by (rule stable_config_after_final_ge_2')
                with \<open>fsn=0\<close> and \<open>steps0 (1, cl', cl) tm n = (fsn, fln, frn)\<close> show ?thesis by auto
              qed
            next
              case False
              then have "stp + 1 \<le> n" by arith
              show ?thesis
              proof -
                from w_fl_fr have "steps0 (1, cl', cl) tm (stp+1) = (0, fl, fr)" by auto
                have "steps0 (1, cl', cl) tm n = (0, fl, fr)"
                proof (rule stable_config_after_final_ge_2')
                  from \<open>steps0 (1, cl', cl) tm (stp+1) = (0, fl, fr)\<close> show "steps0 (1, cl', cl) tm (stp+1) = (0, fl, fr)" by auto
                next
                  from \<open>stp + 1 \<le> n\<close> show "stp + 1 \<le> n" .
                qed
                with \<open>steps0 (1, cl', cl) tm (stp+1) = (0, fl, fr)\<close> show ?thesis by auto
              qed
            qed
          qed
          with w_n' have "is_final(steps0 (1, cl', cl) tm (stp+1)) \<and> Q holds_for steps0 (1, cl', cl) tm (stp+1)" by auto
          moreover from w_fl_fr have "steps0 (1, cl', cl) tm (stp+1) = steps0 (1, cl', cl) (mk_composable0 tm) (stp+1)" by auto
          ultimately have "is_final(steps0 (1, cl', cl) (mk_composable0 tm) (stp+1)) \<and> Q holds_for steps0 (1, cl', cl) (mk_composable0 tm) (stp+1)" by auto
          then show ?thesis by blast
        qed
      qed
      with \<open>tap = (cl', cl)\<close> show "\<exists>n. is_final (steps0 (1, tap) (mk_composable0 tm) n) \<and> Q holds_for steps0 (1, tap) (mk_composable0 tm) n" by auto
    qed
  qed
qed

theorem Hoare_halt_tm_impl_Hoare_halt_mk_composable0_cell_list_generalized: "\<lbrace>P\<rbrace> tm \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> mk_composable0 tm \<lbrace>Q\<rbrace>"
  using Hoare_halt_def Hoare_halt_tm_impl_Hoare_halt_mk_composable0_cell_list_aux old.prod.exhaust by auto
(*------------------------------------------------------------------------------------------------*)

lemma "halting_problem_assuming_dither_copy":
  assumes "\<exists>dither::tprog0. \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <1::nat> @ Bk \<up> l)\<rbrace> dither \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <1::nat> @ Bk \<up> l)\<rbrace>
                          \<and> \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <0::nat> @ Bk \<up> l)\<rbrace> dither \<up>"
  and "\<exists>copy::tprog0. \<forall>n::nat. \<lbrace>\<lambda>tap. tap = ([], <n>)\<rbrace> copy \<lbrace>\<lambda>tap. tap = ([Bk], <(n, n)>)\<rbrace>"

  shows "\<nexists>H. decides_halting H"
proof (rule ccontr)
  assume "\<not> (\<nexists>H::tprog0. decides_halting H)"
  hence "\<exists>H. decides_halting H" by simp

  then obtain H'::tprog0 where "decides_halting H'" ..
  then have "composable_tm0 (mk_composable0 H') \<and> (decides_halting (mk_composable0 H'))"
    using Hoare_halt_tm_impl_Hoare_halt_mk_composable0_cell_list_generalized composable_tm0_mk_composable0 decides_halting_def by blast 
  then have "\<exists>H. composable_tm0 H \<and> decides_halting H" using decides_halting_def by blast
  then obtain H::tprog0 where h: "composable_tm0 H \<and> decides_halting H" ..

  from assms(1) obtain dither::tprog0 where d: "\<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <1::nat> @ Bk \<up> l)\<rbrace> dither \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <1::nat> @ Bk \<up> l)\<rbrace>
                                              \<and> \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <0::nat> @ Bk \<up> l)\<rbrace> dither \<up>" ..

  from assms(2) obtain copy'::tprog0 where "\<forall>n::nat. \<lbrace>\<lambda>tap. tap = ([], <n>)\<rbrace> copy' \<lbrace>\<lambda>tap. tap = ([Bk], <(n, n)>)\<rbrace>" ..
  then have "composable_tm0 (mk_composable0 copy')
          \<and> (\<forall>n::nat. \<lbrace>\<lambda>tap. tap = ([], <n>)\<rbrace> mk_composable0 copy' \<lbrace>\<lambda>tap. tap = ([Bk], <(n, n)>)\<rbrace>)"
    using Hoare_halt_tm_impl_Hoare_halt_mk_composable0_cell_list composable_tm0_mk_composable0 by blast
  then have "\<exists>copy. composable_tm0 copy
          \<and> (\<forall>n::nat. \<lbrace>\<lambda>tap. tap = ([], <n>)\<rbrace> copy \<lbrace>\<lambda>tap. tap = ([Bk], <(n, n)>)\<rbrace>)" by blast
  then obtain copy::tprog0 where c: "composable_tm0 copy 
                                  \<and> (\<forall>n::nat. \<lbrace>\<lambda>tap. tap = ([], <n>)\<rbrace> copy \<lbrace>\<lambda>tap. tap = ([Bk], <(n, n)>)\<rbrace>)" ..

  let ?contra = "copy |+| H |+| dither"
  show "False"
  proof cases
    assume contra_halts: "halts ?contra (tm_to_nat ?contra)"

    from c have p1: "\<lbrace>\<lambda>tap. tap = ([], <tm_to_nat ?contra>)\<rbrace>
                      copy
                     \<lbrace>\<lambda>tap. tap = ([Bk], <(tm_to_nat ?contra, tm_to_nat ?contra)>)\<rbrace>" by simp
    from h contra_halts have p2: "\<lbrace>\<lambda>tap. tap = ([Bk], <(tm_to_nat ?contra, tm_to_nat ?contra)>)\<rbrace>
                                   H
                                  \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <0::nat>  @ Bk \<up> l)\<rbrace>" unfolding decides_halting_def by presburger
    from d have p3: "\<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <0::nat>  @ Bk \<up> l)\<rbrace> dither \<up>" by simp

    from c p1 p2 have p1_2: "\<lbrace>\<lambda>tap. tap = ([], <tm_to_nat ?contra>)\<rbrace>
                              copy |+| H
                             \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <0::nat> @ Bk \<up> l)\<rbrace>" using Hoare_plus_halt by blast
    from c h p1_2 p3 have "\<lbrace>\<lambda>tap. tap = ([], <tm_to_nat ?contra>)\<rbrace> ?contra \<up>"
      using Hoare_plus_unhalt decides_halting_def seq_tm_composable by blast

    then show ?thesis using contra_halts halts_def Hoare_unhalt_impl_not_Hoare_halt by blast
  next
    assume contra_unhalts: "\<not> halts ?contra (tm_to_nat ?contra)"
    hence contra_unhalts_unf: "\<lbrace>\<lambda>tap. tap = ([], <tm_to_nat ?contra>)\<rbrace> ?contra \<up>" using not_halts by blast

    from c have p1: "\<lbrace>\<lambda>tap. tap = ([], <tm_to_nat ?contra>)\<rbrace>
                      copy
                     \<lbrace>\<lambda>tap. tap = ([Bk], <(tm_to_nat ?contra, tm_to_nat ?contra)>)\<rbrace>" by simp
    from h contra_unhalts have p2: "\<lbrace>\<lambda>tap. tap = ([Bk], <(tm_to_nat ?contra, tm_to_nat ?contra)>)\<rbrace>
                                     H
                                    \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <1::nat> @ Bk \<up> l)\<rbrace>" unfolding decides_halting_def by presburger
    from d have p3: "\<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <1::nat> @ Bk \<up> l)\<rbrace> dither \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <1::nat> @ Bk \<up> l)\<rbrace>" by simp

    from c p1 p2 have p1_2: "\<lbrace>\<lambda>tap. tap = ([], <tm_to_nat ?contra>)\<rbrace>
                              copy |+| H
                             \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <1::nat> @ Bk \<up> l)\<rbrace>" using Hoare_plus_halt by blast
    from c h p1_2 p3 have "\<lbrace>\<lambda>tap. tap = ([], <tm_to_nat ?contra>)\<rbrace> ?contra \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <1::nat> @ Bk \<up> l)\<rbrace>"
      using Hoare_plus_halt decides_halting_def seq_tm_composable by blast

    then show ?thesis using contra_unhalts_unf Hoare_halt_impl_not_Hoare_unhalt by blast
  qed
qed

theorem "halting_problem": "\<nexists> H. decides_halting H"
  using One_nat_def append.simps(1) append.simps(2) replicate.simps(1) replicate.simps(2)
        tape_of_nat_def tm_copy_correct tm_dither_halts'' tm_dither_loops''
        halting_problem_assuming_dither_copy
  by auto


text \<open>
  11. Cantor in locales and a new interpretation of the halting problem.
\<close>
definition ocomp :: "(nat\<rightharpoonup>nat) \<Rightarrow> (nat\<rightharpoonup>nat) \<Rightarrow> (nat\<rightharpoonup>nat)" (infixl "\<oplus>" 55) where
"ocomp f\<^sub>1 f\<^sub>2 x = (case f\<^sub>2 x of None \<Rightarrow> None | Some y \<Rightarrow> f\<^sub>1 y)"

lemma ocomp_assoc [simp]: "a \<oplus> (b \<oplus> c) = a \<oplus> b \<oplus> c"
  unfolding ocomp_def
  by (metis option.case_eq_if)

lemma "a \<oplus> Some = a"
  unfolding ocomp_def
  using option.simps(5) by force

lemma "(\<lambda>_.None) \<oplus> a = (\<lambda>_.None)"
  unfolding ocomp_def
  by (simp add: option.case_eq_if)

lemma "a \<oplus> (\<lambda>_.None) = (\<lambda>_.None)"
  unfolding ocomp_def
  by (simp add: option.case_eq_if)

locale computable_universe_carrier =
  fixes F :: "(nat\<rightharpoonup>nat) set"
  fixes pull_up :: "(nat\<rightharpoonup>nat) \<Rightarrow> nat"
  
  assumes countable: "inj_on pull_up F"
  assumes comp_closed: "\<lbrakk>a \<in> F; b \<in> F\<rbrakk> \<Longrightarrow> a \<oplus> b \<in> F"
begin
  definition "naked_push_down \<equiv> inv_into F pull_up"
  definition "push_down x = (case x of Some n \<Rightarrow> (if \<exists>f. pull_up f = n then naked_push_down n else (\<lambda>_.None)) | None \<Rightarrow> (\<lambda>_.None))"

  lemma push_pull_inv [simp]: "\<forall>f \<in> F. push_down (Some (pull_up f)) = f"
    using countable inv_into_f_f naked_push_down_def option.case(2) push_down_def by force

  lemma sanity_pushing_down_1: "\<exists>f. pull_up f = n \<longrightarrow> push_down (Some n) = f"
    by blast
end

locale computable_universe_curried = computable_universe_carrier +
  fixes \<alpha> \<Delta> :: "(nat\<rightharpoonup>nat)"

  assumes alpha_in_f: "\<alpha> \<in> F"
  assumes alpha: "\<alpha> 1 = None" "\<alpha> 0 = Some 1"


  assumes delta_in_f: "\<Delta> \<in> F"
  assumes delta: "\<And>f. f \<in> F \<Longrightarrow> (f \<oplus> \<Delta>) x = (push_down (f x)) x"
begin
  theorem locale_cantor:
  fixes H :: "(nat\<rightharpoonup>nat)"

  assumes Hf_falls_in_F: "\<And>f h. f \<in> F \<Longrightarrow> H (pull_up f) = Some (pull_up h) \<Longrightarrow> h \<in> F"
  assumes H_behaviour: "\<forall>f \<in> F. H (pull_up f) = Some (pull_up (\<lambda>c. case f c of Some _ \<Rightarrow> Some 1 | None \<Rightarrow> Some 0))"

  shows "H \<notin> F"
  proof (rule ccontr)
    assume "\<not> (H \<notin> F)"
    hence "H \<in> F" by simp

    define contra where "contra = \<alpha> \<oplus> H \<oplus> \<Delta>"
    have contra_in_F: "contra \<in> F" by (simp add: \<open>H \<in> F\<close> alpha_in_f comp_closed contra_def delta_in_f)

    have "\<forall>h. H (pull_up contra) = Some (pull_up h) \<longrightarrow> h \<in> F" using Hf_falls_in_F contra_in_F
      by fastforce
    moreover
    have h_pull_up_contra: "H (pull_up contra) = Some (pull_up (\<lambda>c. case contra c of Some _ \<Rightarrow> Some 1 | None \<Rightarrow> Some 0))"
      using H_behaviour contra_in_F by presburger
    ultimately
    have hcontra_in_F: "(\<lambda>c. case contra c of Some _ \<Rightarrow> Some 1 | None \<Rightarrow> Some 0) \<in> F"
      by blast
    
    have possible_pushed_H: "\<And>c. (push_down (H (pull_up contra))) c = Some 1 \<or> (push_down (H (pull_up contra))) c = Some 0"
      by (metis h_pull_up_contra hcontra_in_F option.case_eq_if push_pull_inv)

    show "False"
    proof cases
      assume one: "(push_down (H (pull_up contra))) (pull_up contra) = Some 1"

      hence "(\<lambda>c. case contra c of Some _ \<Rightarrow> Some 1 | None \<Rightarrow> Some 0) (pull_up contra) = Some 1"
        by (metis h_pull_up_contra hcontra_in_F option.case_eq_if option.case_eq_if option.sel push_pull_inv zero_neq_one)
      hence contra_some: "\<exists>n. contra (pull_up contra) = Some n"
        using one_neq_zero option.case_eq_if option.collapse option.inject by fastforce

      have "contra (pull_up contra) = \<alpha> (the ((H \<oplus> \<Delta>) (pull_up contra)))"
        by (metis \<open>H \<in> F\<close> alpha(1) contra_def delta ocomp_assoc ocomp_def one option.sel option.simps(5))
      moreover
      have "\<alpha> (the ((H \<oplus> \<Delta>) (pull_up contra))) = \<alpha> (the (push_down (H (pull_up contra)) (pull_up contra)))"
        by (simp add: \<open>H \<in> F\<close> delta)
      moreover
      have "\<alpha> (the (push_down (H (pull_up contra)) (pull_up contra))) = \<alpha> 1"
        by (simp add: one)
      ultimately
      have contra_none: "contra (pull_up contra) = None"
        using alpha(1) by presburger
      
      show "False" using contra_some contra_none by simp
    next
      assume not_one: "(push_down (H (pull_up contra))) (pull_up contra) \<noteq> Some 1"

      hence zero: "(push_down (H (pull_up contra))) (pull_up contra) = Some 0"
        using possible_pushed_H by auto
      hence "(\<lambda>c. case contra c of Some _ \<Rightarrow> Some 1 | None \<Rightarrow> Some 0) (pull_up contra) = Some 0"
        by (metis not_one h_pull_up_contra hcontra_in_F option.case_eq_if option.case_eq_if push_pull_inv)
      hence contra_none: "contra (pull_up contra) = None"
        by (smt (verit, ccfv_SIG) not_one option.case_eq_if possible_pushed_H)

      have "contra (pull_up contra) = \<alpha> (the ((H \<oplus> \<Delta>) (pull_up contra)))"
        by (metis \<open>H \<in> F\<close> alpha(2) computable_universe_curried.delta computable_universe_curried_axioms contra_def not_one ocomp_assoc ocomp_def option.sel option.simps(5) possible_pushed_H)
      moreover
      have "\<alpha> (the ((H \<oplus> \<Delta>) (pull_up contra))) = \<alpha> (the (push_down (H (pull_up contra)) (pull_up contra)))"
        by (simp add: \<open>H \<in> F\<close> delta)
      moreover
      have "\<alpha> (the (push_down (H (pull_up contra)) (pull_up contra))) = \<alpha> 0"
        by (simp add: zero)
      ultimately
      have contra_some: "\<exists>n. contra (pull_up contra) = Some n"
        using alpha(2) by fastforce

      show "False" using contra_none contra_some by simp
    qed
  qed
end

locale computable_universe_paired = computable_universe_carrier +
  fixes \<alpha> \<Delta>:: "(nat\<rightharpoonup>nat)"
  fixes pair_to_nat :: "(nat \<times> nat) \<Rightarrow> nat"

  assumes alpha_in_f: "\<alpha> \<in> F"
  assumes alpha: "\<alpha> 0 = None" "\<alpha> 1 = Some 1"


  assumes delta_in_f: "\<Delta> \<in> F"
  assumes delta: "\<And>f. f \<in> F \<Longrightarrow> (f \<oplus> \<Delta>) x = f (pair_to_nat (x, x))"
begin
  theorem locale_cantor:
    fixes H :: "(nat\<rightharpoonup>nat)"

    assumes H_behaviour: "\<And>f (c::nat). f \<in> F \<Longrightarrow>  H (pair_to_nat (pull_up f, c)) = (case f c of Some _ \<Rightarrow> Some 0 | None \<Rightarrow> Some 1)"

    shows "H \<notin> F"
  proof (rule ccontr)
    assume "\<not> H \<notin> F"
    hence "H \<in> F" by simp

    define contra where "contra = \<alpha> \<oplus> H \<oplus> \<Delta>"
    have contra_in_F: "contra \<in> F" by (simp add: \<open>H \<in> F\<close> alpha_in_f comp_closed contra_def delta_in_f)

    have possible_H: "H (pair_to_nat ((pull_up contra), (pull_up contra))) = Some 1 \<or> H (pair_to_nat ((pull_up contra), (pull_up contra))) = Some 0"
      by (simp add: alpha(2) assms contra_in_F option.case_eq_if)

    show "False"
    proof cases
      assume zero: "H (pair_to_nat ((pull_up contra), (pull_up contra))) = Some 0"
      hence contra_some: "\<exists>n. contra (pull_up contra) = Some n"
        by (metis UNIV_I assms chi_fun_0_iff chi_fun_1_I contra_in_F option.exhaust_sel option.simps(4))

      have "contra (pull_up contra) = \<alpha> (the ((H \<oplus> \<Delta>) (pull_up contra)))"
        by (metis contra_some contra_def ocomp_assoc ocomp_def option.case_eq_if option.distinct(1) option.simps(4))
      moreover
      have "\<alpha> (the ((H \<oplus> \<Delta>) (pull_up contra))) = \<alpha> (the (H (pair_to_nat ((pull_up contra), (pull_up contra)))))"
        by (simp add: \<open>H \<in> F\<close> delta)
      moreover
      have "\<alpha> (the (H (pair_to_nat ((pull_up contra), (pull_up contra))))) = \<alpha> 0"
        by (simp add: zero option.sel)
      ultimately
      have contra_none: "contra (pull_up contra) = None"
        using alpha(1) by presburger

      show "False" using contra_some contra_none by simp
    next
      assume not_zero: "H (pair_to_nat ((pull_up contra), (pull_up contra))) \<noteq> Some 0"
      hence one: "H (pair_to_nat ((pull_up contra), (pull_up contra))) = Some 1" using possible_H by blast
      hence contra_none: "contra (pull_up contra) = None"
        by (metis assms contra_in_F  not_zero option.case_eq_if)

      have "contra (pull_up contra) = \<alpha> (the ((H \<oplus> \<Delta>) (pull_up contra)))"
        by (metis \<open>H \<in> F\<close> contra_def delta ocomp_assoc ocomp_def option.sel option.simps(5) one)
      moreover
      have "\<alpha> (the ((H \<oplus> \<Delta>) (pull_up contra))) = \<alpha> (the (H (pair_to_nat ((pull_up contra), (pull_up contra)))))"
        by (simp add: \<open>H \<in> F\<close> delta)
      moreover
      have "\<alpha> (the (H (pair_to_nat ((pull_up contra), (pull_up contra))))) = \<alpha> 1"
        by (simp add: one option.sel)
      ultimately
      have contra_some: "\<exists>n. contra (pull_up contra) = Some n"
        using alpha(2) by auto

      show "False" using contra_some contra_none by simp
    qed
  qed
end

(*Turing carrier set -- TODO: add blanks to input/output tapes. check with peter about the soundness of the definition*)
definition induce_F_from_tprog0 :: "tprog0 \<Rightarrow> nat \<Rightarrow> nat option" where
"induce_F_from_tprog0 p inp = (if (\<exists>n c (r::nat) k1 k2 l1 l2. is_final (steps0 (1, (Bk \<up> k1, <inp> @ Bk \<up> l1)) p n) \<and> steps0 (1, (Bk \<up> k1, <inp> @ Bk \<up> l1)) p n = (c, Bk \<up> k2, <r> @ Bk \<up> l2))
                               then Some (SOME r. \<exists>n c k1 k2 l1 l2. steps0 (1, (Bk \<up> k1, <inp> @ Bk \<up> l1)) p n = (c, Bk \<up> k2, <r> @ Bk \<up> l2))
                               else None)"

(*\<exists>n c r k1 k2 l1 l2. is_final (steps0 (1, (Bk \<up> k1, <inp> @ Bk \<up> l1)) p n) \<and> steps0 (1, (Bk \<up> k1, <inp> @ Bk \<up> l1)) p n = (c, Bk \<up> k2, <r> @ Bk \<up> l2)*)

definition turing_F :: "(nat\<rightharpoonup>nat) set" where
"turing_F = induce_F_from_tprog0 ` {p. composable_tm0 p}"

lemma composable_tprog_in_turing_F: "\<And>p. composable_tm0 p \<Longrightarrow> induce_F_from_tprog0 p \<in> turing_F"
  by (simp add: image_eqI turing_F_def)

(*Carrier set functions back to Turing and then to nat*)
definition turing_pull_up :: "(nat\<rightharpoonup>nat) \<Rightarrow> nat" where
"turing_pull_up f = (if f \<in> turing_F then tm_to_nat (SOME p. induce_F_from_tprog0 p = f) else 0)"

lemma countable_turing_F: "inj_on turing_pull_up turing_F"
  unfolding inj_on_def turing_pull_up_def using inj_tm_to_nat
  by (smt (verit, del_insts) Collect_cong Collect_mem_eq Eps_cong UNIV_I UNIV_def halting_problem
      imageE mem_Collect_eq nat_to_tm_is_inv_of_tm_to_nat someI_ex some_eq_ex turing_F_def
      turing_pull_up_def verit_sko_ex' verit_sko_forall)

(*turing_F closed under \<oplus> and equivalent with |+|*)
lemma turing_F_from_composable_tm: "\<And>a. a \<in> turing_F \<Longrightarrow> \<exists>p. (composable_tm0 p) \<and> (induce_F_from_tprog0 p = a)"
  by (metis (no_types, lifting) f_inv_into_f inv_into_into mem_Collect_eq turing_F_def)

lemma seq_tm_stays_in_turing_F: "\<And>p1 p2. composable_tm0 p1 \<Longrightarrow> composable_tm0 p2 \<Longrightarrow> induce_F_from_tprog0 (p2 |+| p1) \<in> turing_F"
  using seq_tm_composable composable_tprog_in_turing_F by blast

lemma seq_tm_oplus_correspondence: "\<And>p1 p2. composable_tm0 p1 \<Longrightarrow> composable_tm0 p2 \<Longrightarrow>
        induce_F_from_tprog0 (p2 |+| p1) = (induce_F_from_tprog0 p1) \<oplus> (induce_F_from_tprog0 p2)"
  sorry

lemma closed_turing_F: "\<And>a b. a \<in> turing_F \<Longrightarrow> b \<in> turing_F \<Longrightarrow> a \<oplus> b \<in> turing_F"
  by (metis (no_types, lifting) composable_tprog_in_turing_F seq_tm_oplus_correspondence f_inv_into_f inv_into_into mem_Collect_eq seq_tm_composable turing_F_def)

(*Invoke the first half*)
interpretation computable_universe_carrier turing_F turing_pull_up
  apply unfold_locales
  apply (simp add: countable_turing_F)
  apply (simp add: closed_turing_F)
  done

(*Invoke the second half*)
lemma countable_tape: "from_nat (to_nat (tp::tape)) = tp"
  by simp

fun pair_plus :: "(nat \<times> nat) \<Rightarrow> nat" where
"pair_plus (t1, t2) = t1 + t2"

definition "turing_dither = induce_F_from_tprog0 tm_dither"

lemma turing_dither_in_turing_F: "turing_dither \<in> turing_F"
  unfolding turing_dither_def
  using composable_tm0_tm_dither composable_tprog_in_turing_F
  by blast

definition tm_doubling :: "tprog0" where
"tm_doubling = [(WO, 2), (R, 1), (L, 3), (R, 2), (WB, 0), (WB, 0)]"

lemma tm_doubling_removes_Bk: "\<lbrace>\<lambda>tap. tap = ([Bk], <(x::nat, x)>)\<rbrace> tm_doubling \<lbrace>\<lambda>tap. \<exists>l. tap = ([Bk], <(x + x)> @ Bk \<up> l)\<rbrace>"
  sorry

lemma composable_tm0_tm_doubling[intro, simp]: "composable_tm0 tm_doubling"
  by (auto simp: tm_doubling_def)

definition "tm_modified_copy = tm_copy |+| tm_doubling"

lemma oc_arrow_to_encode: "Oc \<up> (Suc n) = <n>"
  by (simp add: tape_of_nat_def)

lemma tm_modified_copy_hoare: "\<lbrace>\<lambda>tap. tap = ([], <x::nat>)\<rbrace> tm_modified_copy \<lbrace>\<lambda>tap. \<exists>l. tap = ([Bk], <(x + x)> @ Bk \<up> l)\<rbrace>"
  using tm_modified_copy_def tm_doubling_removes_Bk tm_copy_correct oc_arrow_to_encode
  Hoare_plus_halt composable_tm0_tm_copy Hoare_halt_def
  by (metis (no_types, lifting))

lemma composable_tm0_tm_modified_copy[intro, simp]: "composable_tm0 tm_modified_copy"
  by (metis composable_tm0_tm_copy composable_tm0_tm_doubling seq_tm_composable tm_modified_copy_def)

definition "turing_copy = induce_F_from_tprog0 tm_modified_copy"

lemma turing_copy_in_turing_F: "turing_copy \<in> turing_F"
  using composable_tm0_tm_modified_copy composable_tprog_in_turing_F turing_copy_def
  by presburger

lemma turing_dither_halts: "turing_dither 1 = Some 1"
  sorry

lemma turing_dither_loops: "turing_dither 0 = None"
  sorry

lemma turing_copy_copies: "\<And>f x. f \<in> turing_F \<Longrightarrow> (f \<oplus> turing_copy) x = f (pair_plus (x, x))"
  sorry

interpretation computable_universe_paired turing_F turing_pull_up turing_dither turing_copy pair_plus
  apply unfold_locales
  using turing_dither_in_turing_F apply simp
  using turing_dither_loops apply simp
  using One_nat_def turing_dither_halts apply fastforce
  using turing_copy_in_turing_F apply simp
  using turing_copy_copies apply simp
  done

end
