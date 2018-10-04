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

\<comment>\<open>Takes a list of weights, a partially filled bin and the current list of bin assignments,
   and returns a list of bin assignments.\<close>
fun nf_aux' :: "real list \<Rightarrow> nat \<times> real \<Rightarrow> nat list \<Rightarrow> nat list" where
  "nf_aux' []       _       bs = bs"
| "nf_aux' (w # ws) (b , u) bs = (if u + w \<le> cp
                                  then nf_aux' ws (b , u + w) (bs @ [b])
                                  else nf_aux' ws (1 + b , w) (bs @ [b + 1]))"
fun alg_aux :: "real list \<Rightarrow> nat \<times> real \<Rightarrow> nat list" where
  "alg_aux []       _       = []"
| "alg_aux (w # ws) (b , u) = (if u + w \<le> cp
                               then b # alg_aux ws (b , u + w)
                               else (1 + b) # alg_aux ws (1 + b , w))"
definition alg :: "real list \<Rightarrow> nat list" where
  "alg ws = alg_aux ws (0 , 0)"

abbreviation ws1 :: "real list" where "ws1 == [0.2,0.5,0.4,0.7,0.1,0.3,0.8]"
value "alg ws1 = [0,0,1,2,2,3,4]"
value "alg [1,1] = [0,1]"

lemma assigns_all1: "length (alg ws) = length ws"
  unfolding alg_def
  by (induction ws _ rule: alg_aux.induct; simp)

lemma assigns_all2: "i < length ws \<Longrightarrow> bin (alg ws) i \<in> set (alg ws)"
  unfolding bin_def
  by (auto simp add: assigns_all1)

\<comment>\<open>Takes a list of weights and bin assignments and a bin number,
   and returns the used capacity.\<close>
definition bu :: "(real \<times> nat) list \<Rightarrow> nat \<Rightarrow> real" where
  "bu wb b = sum [w. (w,b') \<leftarrow> wb, b' = b]"

lemma [simp]: "bu [] b = 0" by (simp add: bu_def)
lemma [simp]: "bu ((w,b) # wb) b = w + bu wb b" by (simp add: bu_def)
lemma [simp]: "b \<noteq> b' \<Longrightarrow> bu ((w,b') # wb) b = bu wb b" by (simp add: bu_def)

lemma respects_cp0[simp]: "b < b' \<Longrightarrow> bu (zip ws (alg_aux ws (b' , u))) b = 0"
  by (induction ws arbitrary: b' u; simp)

lemma respects_cp1: "list_all (\<lambda>w. w \<le> cp) ws \<Longrightarrow> u \<le> cp \<Longrightarrow> bu (zip ws (alg_aux ws (b , u))) b \<le> cp - u"
proof (induction ws arbitrary: u)
  case Nil
  thus ?case by simp
next
  case (Cons w ws)
  hence "list_all (\<lambda>w. w \<le> cp) ws" by simp
  note IH = Cons.IH[OF this]
  show ?case
  proof cases
    assume ass: "u + w \<le> cp"
    then have "alg_aux (w # ws) (b , u) = b # alg_aux ws (b , u + w)" by simp
    also have "zip (w # ws) ... = (w , b) # zip ws (alg_aux ws (b , u + w))" by simp
    also have "bu ... b = w + bu (zip ws (alg_aux ws (b , u + w))) b" by simp
    also have "... \<le> w + (cp - (u + w))" using IH[OF ass] by simp
    also have "... = cp - u" by simp
    finally show ?case .
  next
    assume "\<not> u + w \<le> cp"
    then have "alg_aux (w # ws) (b , u) = (b + 1) # alg_aux ws (b + 1 , w)" by simp
    also have "zip (w # ws) ... = (w , b + 1) # zip ws (alg_aux ws (b + 1 , w))" by simp
    also have "bu ... b = bu (zip ws (alg_aux ws (b + 1 , w))) b" by simp
    also have "... = 0" by simp
    also have "... \<le> cp - u" using \<open>u\<le>cp\<close> by simp
    finally show ?case .
  qed
qed

lemma respects_cp2: "list_all (\<lambda>w. w \<le> cp) ws \<Longrightarrow> b > b' \<Longrightarrow> bu (zip ws (alg_aux ws (b' , u))) b \<le> cp"
proof (induction ws arbitrary: u b')
  case Nil
  show ?case by simp
next
  case (Cons w ws)
  hence "w \<le> cp" and "list_all (\<lambda>w. w \<le> cp) ws" and "b' \<noteq> b" by auto
  note IH = Cons.IH[OF this(2)] and respects_cp1 = respects_cp1[OF this(2) this(1)]
  show ?case
  proof cases
    assume "u + w \<le> cp"
    then have "alg_aux (w # ws) (b' , u) = b' # alg_aux ws (b' , u + w)" by simp
    also have "zip (w # ws) ... = (w , b') # zip ws (alg_aux ws (b' , u + w))" by simp
    also have "bu ... b = bu (zip ws (alg_aux ws (b' , u + w))) b" using \<open>b'\<noteq>b\<close> by simp
    also have "... \<le> cp" using IH[OF \<open>b'<b\<close>] by simp
    finally show ?case .
  next
    assume "\<not> u + w \<le> cp"
    then have "alg_aux (w # ws) (b' , u) = (b' + 1) # alg_aux ws (b' + 1 , w)" by simp
    also have "zip (w # ws) ... = (w , b' + 1) # zip ws (alg_aux ws (b' + 1 , w))" by simp
    also have "bu ... b \<le> cp"
    proof cases
      assume "b > b' + 1"
      hence "bu ((w , b' + 1) # zip ws (alg_aux ws (b' + 1 , w))) b = bu (zip ws (alg_aux ws (b' + 1 , w))) b" by simp
      also have "... \<le> cp" using IH[OF \<open>b>b'+1\<close>] by simp
      finally show ?thesis .
    next
      assume "\<not> b > b' + 1"
      with \<open>b>b'\<close> have "b = b' + 1" by simp
      hence "bu ((w , b' + 1) # zip ws (alg_aux ws (b' + 1 , w))) b = w + bu (zip ws (alg_aux ws (b' + 1 , w))) (b' + 1)" by simp
      also have "bu (zip ws (alg_aux ws (b' + 1 , w))) (b' + 1) \<le> cp - w" using respects_cp1 by simp
      also have "w + ... = cp" by simp
      finally show ?thesis by simp
    qed
    finally show ?case .
  qed
qed
end