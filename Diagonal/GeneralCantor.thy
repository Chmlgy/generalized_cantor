section \<open>Generalized Cantor's Theorem and Instances\<close>

theory GeneralCantor imports Complex_Main "HOL-Library.Countable" "HOL-Analysis.Analysis"
  "HOL-ZF.HOLZF" "~~/afp-2023-05-17/thys/Universal_Turing_Machine/HaltingProblems_K_H"
  "~~/afp-2023-05-17/thys/Universal_Turing_Machine/Turing_aux"
  "~~/afp-2023-05-17/thys/Universal_Turing_Machine/Numerals_Ex"
  "~~/afp-2023-05-17/thys/Universal_Turing_Machine/TuringDecidable"
  "~~/afp-2023-05-17/thys/Universal_Turing_Machine/HaltingProblems_K_aux"
  "~~/afp-2023-05-17/thys/Universal_Turing_Machine/TuringComputable"
  "~~/afp-2023-05-17/thys/Universal_Turing_Machine/DitherTM"
  "~~/afp-2023-05-17/thys/Universal_Turing_Machine/CopyTM"
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
proof -
  have forward: "(\<forall>\<alpha> :: 'b \<Rightarrow> 'b. \<exists>y. \<alpha> y = y) \<longrightarrow> (\<forall>a b :: 'b. a = b)" using fixed_to_one_elem by simp
  have backward: "(\<forall>a b :: 'b. a = b) \<longrightarrow> (\<forall>\<alpha> :: 'b \<Rightarrow> 'b. \<exists>y. \<alpha> y = y)" using one_elem_to_fixed by simp
  thus ?thesis using forward backward by metis
qed


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

theorem "Non-re_Languages":
  assumes surjectivity: "surj TMC_has_num_list_res"
  shows "False"
  apply(rule Abstracted_Cantor[of TMC_has_num_list_res Not nat_list_to_tm tm_to_nat_list])
  apply(auto simp add: surjectivity nat_list_to_tm_is_inv_of_tm_to_nat_list)
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
  using Hoare_unhaltI halts_alt_def by presburger

lemma not_halts_alt: "\<not> halts p ns \<longrightarrow> (\<nexists>n. is_final (steps0 (1, [], <ns>) p n))"
  using halts_def Hoare_halt_def
  by blast

definition "decides_halting H \<equiv> (\<forall>(p::tprog0) (ns::nat).
  \<lbrace>\<lambda>tap. tap = ([Bk], <(tm_to_nat p, ns)>)\<rbrace>
   H
  \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <(if halts p ns then 0::nat else 1::nat)> @ Bk \<up> l)\<rbrace>)"

(*TODO: AFP entry should include this.*)
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
(*------------------------------------*)

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

theorem "halting_problem":
  shows "\<nexists> H. decides_halting H"
  using One_nat_def append.simps(1) append.simps(2) replicate.simps(1) replicate.simps(2)
        tape_of_nat_def tm_copy_correct tm_dither_halts'' tm_dither_loops''
        halting_problem_assuming_dither_copy by auto


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

lemma "Some \<oplus> a = a"
  unfolding ocomp_def
  by (metis option.case_eq_if option.exhaust_sel option.simps(4))

lemma "(\<lambda>_. None) \<oplus> a = (\<lambda>_. None)"
  unfolding ocomp_def
  by (simp add: option.case_eq_if option.simps(4))

lemma "a \<oplus> (\<lambda>_. None) = (\<lambda>_. None)"
  unfolding ocomp_def
  by (simp add: option.simps(4))

locale computable_universe_carrier =
     fixes F :: "(nat\<rightharpoonup>nat) set" (*No assumption on the size of F, maybe we want it to be infinite?*)
     fixes pull_up :: "(nat\<rightharpoonup>nat) \<Rightarrow> nat"
     (*fixes push_down :: "nat \<Rightarrow> (nat\<rightharpoonup>nat)"*)

     assumes id_in_F: "Some \<in> F"
     assumes bot_in_F: "(\<lambda>_. None) \<in> F"
     assumes countable: "inj_on pull_up F" (*Each member of F is mapped to a unique natural number*)
     assumes comp_closed: "\<lbrakk>a \<in> F; b \<in> F\<rbrakk> \<Longrightarrow> a \<oplus> b \<in> F"
begin
  definition push_down :: "nat \<Rightarrow> (nat \<rightharpoonup> nat)" where "push_down \<equiv> inv_into F pull_up"

  lemma push_pull_inv [simp]: "f \<in> F \<Longrightarrow> push_down (pull_up f) = f"
    unfolding push_down_def
    using countable
    by simp

  definition "f_curryable = {f \<in> F. (\<forall>x gn. f x = Some gn \<longrightarrow> push_down gn \<in> F)}"
end

locale computable_universe = computable_universe_carrier +
  fixes \<alpha> \<Delta> :: "(nat\<rightharpoonup>nat)"

  assumes "\<alpha> \<in> F"
  assumes "\<alpha> 1 = None" "\<alpha> 0 = Some 1"

  assumes "\<Delta> \<in> F"
  assumes copy: "\<And>f. f \<in> f_curryable \<Longrightarrow> (f \<oplus> \<Delta>) x = (case f x of None \<Rightarrow> None | Some gn \<Rightarrow> (push_down gn) x)"
begin
  (*definition "H_partial x = (\<lambda>c. case (push_down x) c of Some _ \<Rightarrow> Some 1 | None \<Rightarrow> Some 0)"*)
  definition "H x = Some (pull_up (\<lambda>c. case (push_down x) c of Some _ \<Rightarrow> Some 1 | None \<Rightarrow> Some 0))"

  (*
  lemma possible_h_partial: "H_partial x c = Some 1 \<or> H_partial x c = Some 0"
    unfolding H_partial_def
    by (simp add: option.case_eq_if)
  *)

  theorem locale_cantor: "H \<notin> F"
  proof (rule ccontr)
    note [[show_types]]
    assume "\<not> (H \<notin> F)"
    hence "H \<in> F" by simp

    define contra where "contra = \<alpha> \<oplus> H \<oplus> \<Delta>"

    show "False"
    proof cases
      assume "(H_partial (pull_up contra)) (pull_up contra) = Some 1"
      hence contra_some: "\<exists>n. contra (pull_up contra) = Some n"
        by (metis H_partial_def \<open>H \<in> (F::(nat \<Rightarrow> nat option) set)\<close> comp_closed computable_universe.axioms(2)
                  computable_universe_axioms computable_universe_axioms_def contra_def is_none_code(2)
                  ocomp_assoc option.case_eq_if option.inject option.split_sel_asm push_pull_inv zero_neq_one)

      have contra_none: "contra (pull_up contra) = None" sorry

      show "False" using contra_some contra_none by simp
    next
      assume "(H_partial (pull_up contra)) (pull_up contra) \<noteq> Some 1"
      hence "(H_partial (pull_up contra)) (pull_up contra) = Some 0" using possible_h_partial by blast
      hence contra_none: "contra (pull_up contra) = None"
        by (metis H_partial_def \<open>H \<in> (F::(nat \<Rightarrow> nat option) set)\<close>
                  \<open>H_partial ((pull_up::(nat \<Rightarrow> nat option) \<Rightarrow> nat) (contra::nat \<Rightarrow> nat option)) (pull_up contra) \<noteq> Some (1::nat)\<close>
                  comp_closed computable_universe_axioms computable_universe_axioms_def
                  computable_universe_def contra_def option.case_eq_if push_pull_inv)
      
      have contra_some: "\<exists>n. contra (pull_up contra) = Some n" sorry

      show "False" using contra_none contra_some by simp
    qed
  qed
end

interpretation computable_universe turing_F turing_pull_up turing_dither turing_copy
  apply unfold_locales
  sorry


end
