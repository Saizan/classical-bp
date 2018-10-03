theory BinPacking imports Complex_Main
begin
\<comment>\<open> List.sum is defined indirectly via (finite) sets.\<close>
definition sum :: "'a::comm_monoid_add list \<Rightarrow> 'a" where
  "sum xs = foldr (+) xs 0"

lemma [simp]: "sum [] = 0" by (simp add: sum_def)
lemma [simp]: "sum (a # as) = a + sum as" by (simp add: sum_def)

\<comment>\<open>The standardised bin capacity.\<close>
abbreviation cp :: real where
  "cp \<equiv> 1"

\<comment>\<open>Takes a list of bin assignments and a weight index,
   and returns the bin number.\<close>
definition bin :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "bin bs i = bs ! i"

\<comment>\<open>Takes a list of bin assignments,
   and returns the total number of bins.\<close>
definition bins :: "nat list \<Rightarrow> nat" where
  "bins bs = card (set bs)"

\<comment>\<open>Takes a list of weights and a partially filled bin,
   and returns a list of bin assignments.\<close>
definition alg :: "real list \<Rightarrow> nat list" where
  "alg = undefined"

abbreviation ws1 :: "real list" where "ws1 == [0.2,0.5,0.4,0.7,0.1,0.3,0.8]"
value "alg ws1 = [0,1,1,2,1,2,0]"

lemma assigns_all1: "length (alg ws) = length ws"
  sorry

lemma assigns_all2: "i < length ws \<Longrightarrow> bin (alg ws) i \<in> set (alg ws)"
  sorry

\<comment>\<open>Takes a list of weights and bin assignments and a bin number,
   and returns the used capacity.\<close>
definition bu :: "(real \<times> nat) list \<Rightarrow> nat \<Rightarrow> real" where
  "bu wb b = sum [w. (w,b') \<leftarrow> wb, b' = b]"

lemma [simp]: "bu [] b = 0" by (simp add: bu_def)
lemma [simp]: "bu ((w,b) # wb) b = w + bu wb b" by (simp add: bu_def)
lemma [simp]: "b \<noteq> b' \<Longrightarrow> bu ((w,b') # wb) b = bu wb b" by (simp add: bu_def)

lemma respects_cp: "list_all (\<lambda>w. w \<le> cp) ws \<Longrightarrow> bu (zip ws (alg ws)) b \<le> cp"
  sorry
end