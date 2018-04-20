theory CombinatoricsBackground
  imports Main "$ISABELLE_HOME/src/HOL/Library/FSet" "$ISABELLE_HOME/src/HOL/Orderings"
begin
  
  
  (* This file proves general facts about Finite Sets, Trees, Forests, and Languages *)
  
  (* --------------------------------------------------------- *)
  (* ------- MAXIMA OF FINITE SETS OF NATURAL NUMBERS -------- *)
  (* --------------------------------------------------------- *)
  
    (* immediate generalization of finite_maxlen from List.thy *)
  lemma finite_maxvalue:
  fixes M
  fixes \<ff> :: "'a \<Rightarrow> nat"
  shows  "finite (M::'a set) ==> EX n. ALL s:M. \<ff> s < n"
proof (induct rule: finite.induct)
  case emptyI show ?case by simp
next
  case (insertI M xs)
  then obtain n where "\<forall>s\<in>M. \<ff> s < n" by blast
  hence "ALL s:insert xs M. \<ff> s < max n (\<ff> xs) + 1" by auto
  thus ?case ..
qed
  
  
lemma finite_maxvalue2:
  fixes M
  fixes \<ff> :: "'a \<Rightarrow> nat"
  shows  "finite (M::'a set) ==> EX n. ALL s:M. \<ff> s \<le> n"
proof (induct rule: finite.induct)
  case emptyI show ?case by simp
next
  case (insertI M xs)
  then obtain n where "\<forall>s\<in>M. \<ff> s \<le> n" by blast
  hence "ALL s:insert xs M. \<ff> s \<le> max n (\<ff> xs) " by auto
  thus ?case ..
qed
  
definition maxFset :: "nat fset \<Rightarrow> nat" where "maxFset s = (SOME x. ((\<forall> y. (y|\<in>|s \<longrightarrow> y \<le> x)) \<and> (s = {||} \<longrightarrow> x=0) \<and> (s \<noteq> {||} \<longrightarrow> (x |\<in>| s))))"
  
  
lemma finite_maxvalue3:
  fixes M
  fixes \<ff> :: "'a \<Rightarrow> nat"
  shows  "finite (M::'a set) ==> M \<noteq> {} \<Longrightarrow>  EX n. ALL s:M. \<ff> s \<le> n \<and> n \<in> (\<ff> ` M)"
proof (induct rule: finite.induct)
  case emptyI show ?case by simp
next
  case (insertI M xs)
  then obtain n where b1 : "\<forall>s\<in>M. ((\<ff> s \<le> n) \<and> n \<in> (\<ff> ` M))" by blast
  hence b20 : "ALL s:insert xs M. \<ff> s \<le> max n (\<ff> xs)" by auto
  have b2 : "(\<ff> ` (insert xs M)) = insert (\<ff> xs) (\<ff> ` M)" by simp
      
  show "\<exists>n. \<forall>s\<in>insert xs M. \<ff> s \<le> n \<and> n \<in> \<ff> ` insert xs M"
  proof (rule disjE)
    show "M = {} \<or> M \<noteq> {}" by auto
    show "M = {} \<Longrightarrow> \<exists>n. \<forall>s\<in>insert xs M. \<ff> s \<le> n \<and> n \<in> \<ff> ` insert xs M" by auto
        
    show "M \<noteq> {} \<Longrightarrow> \<exists>n. \<forall>s\<in>insert xs M. \<ff> s \<le> n \<and> n \<in> \<ff> ` insert xs M"
    proof -
      
      have b10 : "M \<noteq> {} \<Longrightarrow> \<exists> element . element \<in> M"  by auto
      from b1 b10 have b3 : "M \<noteq> {} \<Longrightarrow> n \<in> (\<ff> ` M)"        by blast 
      from b2  b3 have b21 : "M \<noteq> {} \<Longrightarrow> max n (\<ff> xs) \<in> (\<ff> ` insert xs M)"      by (simp add: max_def)  
      from b20 b21   have "M \<noteq> {} \<Longrightarrow> \<forall>s\<in>insert xs M. \<ff> s \<le> (max n (\<ff> xs)) \<and> (max n (\<ff> xs)) \<in> \<ff> ` insert xs M" by simp
      then show "M \<noteq> {} \<Longrightarrow> \<exists>n. \<forall>s\<in>insert xs M. \<ff> s \<le> n \<and> n \<in> \<ff> ` insert xs M" by blast
    qed
      
  qed
qed
  
  
lemma finiteMaxExists :
  shows "\<And> t . t |\<in>| s \<Longrightarrow> t \<le> (maxFset s)"
    and "(s = {||} \<Longrightarrow> (maxFset s)=0)"
    and "(s \<noteq> {||} \<Longrightarrow> ((maxFset s) |\<in>| s))"
proof (rule disjE)
  show "s = {||} \<or> (s \<noteq> {||}) " by auto
  have h1 : "finite (fset s)" by auto
  {
    assume k1 : "(s \<noteq> {||}) " 
    then obtain max where "\<And> t . (t |\<in>| s \<Longrightarrow> (t \<le> max \<and> max |\<in>| s))" using h1 finite_maxvalue3  notin_fset  finite_nat_set_iff_bounded less_or_eq_imp_le    by (metis bot_fset.rep_eq fset_inject infinite_growing leI) 
    then have "((\<forall> y. (y|\<in>|s \<longrightarrow> y \<le> max)) \<and> (s = {||} \<longrightarrow> max=0) \<and> (s \<noteq> {||} \<longrightarrow> (max |\<in>| s)))" using k1 by blast
    then have n4775 : "\<exists> max. ((\<forall> y. (y|\<in>|s \<longrightarrow> y \<le> max)) \<and> (s = {||} \<longrightarrow> max=0) \<and> (s \<noteq> {||} \<longrightarrow> (max |\<in>| s)))" by auto
    def P == "\<lambda> max. ((\<forall> y. (y|\<in>|s \<longrightarrow> y \<le> max)) \<and> (s = {||} \<longrightarrow> max=0) \<and> (s \<noteq> {||} \<longrightarrow> (max |\<in>| s)))"
    from n4775 P_def have "\<exists> max. P max" by auto
    then have j90 : "P (SOME x. P x)"       by (simp add: someI_ex) 
    from maxFset_def P_def    have "(SOME x. P x) = maxFset s" by auto
    then have q1 : "((\<forall> y. (y|\<in>|s \<longrightarrow> y \<le> (maxFset s))) \<and> (s = {||} \<longrightarrow> (maxFset s)=0) \<and> (s \<noteq> {||} \<longrightarrow> ((maxFset s) |\<in>| s)))" using j90 P_def by auto
    then show "\<And>t. t |\<in>| s \<Longrightarrow> s \<noteq> {||} \<Longrightarrow> t \<le> maxFset s" by blast
    show  "maxFset s |\<in>| s" using  k1 q1 by auto
  }
  have "(s = {||}) \<Longrightarrow> ((\<forall> y. (y|\<in>|s \<longrightarrow> y \<le> 0)) \<and> (s = {||} \<longrightarrow> 0=0) \<and> (s \<noteq> {||} \<longrightarrow> (0 |\<in>| s)))" by blast
  then have j1 : "(s = {||}) \<Longrightarrow> ((\<forall> y. (y|\<in>|s \<longrightarrow> y \<le> (maxFset s))) \<and> (s = {||} \<longrightarrow> (maxFset s)=0) \<and> (s \<noteq> {||} \<longrightarrow> ((maxFset s) |\<in>| s)))" using someI_ex    using maxFset_def by auto
  then show  "s = {||} \<Longrightarrow> (\<And> t . t |\<in>| s \<Longrightarrow> t \<le> (maxFset s))" using finite_maxvalue2 maxFset_def notin_fset    by (smt someI_ex)
  from j1 show "s = {||} \<Longrightarrow> (maxFset s) = 0" by auto
qed
  
  (* --------------------------------------------------------- *)
  (*  UNIONS OF FINITE SETS OF SETS  *)
  (* --------------------------------------------------------- *)
  
  
lemma  ffUnionLemma :
  fixes a
  fixes b
  assumes "a |\<in>| \<Union>| b "
  obtains c where "c |\<in>| b" and "a |\<in>| c"
  using assms by auto
    
  
  (* --------------------------------------------------------- *)
  (*  STATES, ALPHABETS, TREES  *)
  (* --------------------------------------------------------- *)
  
  
datatype ot = \<aa>\<^sub>1 | \<aa>\<^sub>2
datatype tv = PLACEHOLDER
    
definition numberOfLettersAndStates :: "nat" where "numberOfLettersAndStates = (SOME x. x> 1)"
typedef abc = "{n . n \<le> numberOfLettersAndStates}"  by auto
typedef stt = "{n . n \<le> numberOfLettersAndStates}"  by auto
    (*datatype abc = A "abcIndex"*)
(*datatype stt = B "stateIndex"*)
  
  
  
(*definition asdf :: "nat" where "asdf = (GREATEST x.(x=x))"*)
  
datatype 'l tree = NODE "'l" "'l tree fset"
  
  
  
  
fun childrenSet where "childrenSet (NODE symb2 set2) = set2"
fun root where "root (NODE symb2 set2) = symb2"
  
  
  (* --------------------------------------------------------- *)
  (*  NODES IN TREES, AND SEQUENCES OF NODES  *)
  (* --------------------------------------------------------- *)
  
datatype 'l contxt = cNODE "'l" "'l contxt" "'l tree fset" | PLACEHOLDER 

primrec insertIntoContext where
  "(insertIntoContext tr (cNODE symb contextChild children)) = (NODE symb (finsert (insertIntoContext tr contextChild) children))" |
  "insertIntoContext tr PLACEHOLDER = tr"
  
primrec insertContextIntoContext where
  "(insertContextIntoContext contxt (cNODE symb contextChild children)) = (cNODE symb  (insertContextIntoContext contxt contextChild)  children)" |
  "insertContextIntoContext contxt PLACEHOLDER = contxt"
  
record 'L node =
  up :: "'L contxt"
  down :: "'L tree"
  
  
definition isNodeIn where
  "isNodeIn n tr = ((insertIntoContext (down n) (up n))  = tr)"
definition isRootNode where
  "isRootNode n = ((up n) = PLACEHOLDER)"
definition isLeafNode where
  "isLeafNode n = (childrenSet (down n) = {||})"
definition labelOfNode where
  "labelOfNode n = (root (down n))"
  
  
lemma nodeExists:
  shows "\<exists> node . down node = tr"
  by (meson select_convs(2))
    
    
definition turnIntoContextByRemovingChild where
  "turnIntoContextByRemovingChild tr child = (cNODE (root tr) PLACEHOLDER    ( (childrenSet tr) |-| {|child|}   )  )"
  
definition immediatelyDominates :: "'l node \<Rightarrow> 'l node \<Rightarrow> bool" where
  "immediatelyDominates n1 n2 = (   ((down n2) |\<in>| (childrenSet (down n1))) 
                                  (*\<and> ((up n2) = insertContextIntoContext ( turnIntoContextByRemovingChild (down n1) (down n2)    ) (up n1))*)
                                )"
  
  (* the empty path is not a good path. *)
  (* \<Pi> do not need to go up to a leaf *)
inductive_set isAPath :: "'l node list set" where
  "[node] \<in> isAPath" |
  "path \<in> isAPath \<Longrightarrow> (\<exists>e1.\<exists>tail.(path = (e1#tail)) \<and> immediatelyDominates e2 e1) \<Longrightarrow> e2#path \<in> isAPath"
  
  
  (* the empty path is not a good path *)
definition pathsInTree where
  "pathsInTree tr = {p . (isAPathp p) \<and> (( \<exists>e1.\<exists>tail.(p = (e1#tail) \<and> down e1 = tr)))}" (* \<and> (isNodeIn e1 tr) \<and> (isRootNode e1)        )      ))}"*)
  
lemma noEmptyPaths:
  shows "[] \<notin> isAPath"
  using isAPath.cases by blast
    
lemma noEmptyPathsInTree:
  shows "[] \<notin> pathsInTree tr"
  using noEmptyPaths pathsInTree_def by blast
    
    
    
lemma theSingletonPathExists :
  fixes tree :: "abc tree"
  shows "\<exists>path. \<exists> node. (isAPathp path) \<and> path = [node] \<and> down node = tree \<and> path \<in> pathsInTree tree"
proof -
  from nodeExists obtain node :: "abc node" where a1 : "down node = tree" by auto
  from a1 isAPathp.simps pathsInTree_def have "(isAPathp [node]) \<and> [node] = [node] \<and> down node = tree \<and> [node] \<in> pathsInTree tree" by blast
  then show "\<exists>path. \<exists>node. isAPathp path \<and> path = [node] \<and> down node = tree \<and> path \<in> pathsInTree tree" by blast
qed
  
  (*================================================*)
  
  (*http://stackoverflow.com/questions/28633353/converting-a-set-to-a-list-in-isabelle*)
definition set_to_list :: "'a set \<Rightarrow> 'a list"
  where "set_to_list s = (SOME l. set l = s)"
lemma  set_set_to_list:
  "finite s \<Longrightarrow> set (set_to_list s) = s"
  unfolding set_to_list_def by (metis (mono_tags) finite_list some_eq_ex)
definition set_to_fset :: "'a set \<Rightarrow> 'a fset"
  where "set_to_fset s = Abs_fset s"
    
    
definition emptyTree :: "'L tree" where
  "emptyTree = (NODE (SOME x.(x=x)) fempty )"
  
  (* --------------------------------------------------------- *)
  (*  TREE AUTOMATA AND RECOGNITION OF TREE LANGUAGES  *)
  (* --------------------------------------------------------- *)
  
subsection "Tree Automata"
  
record ('Q,'L) rule =
  states :: "'Q fset"
  symbol :: "'L"
    
  -- "Finite Tree \<A>omata"
record ('Q,'L) tree_automaton =
  transition :: "'Q fset \<Rightarrow> 'L \<Rightarrow> 'Q"
  rule_set :: "('Q,'L) rule fset"
  
definition state_set :: "('Q,'L) tree_automaton \<Rightarrow> 'Q fset" where "state_set automaton = ((Abs_fset UNIV) :: ('Q fset))"
  
   
definition is_tree_automaton :: "('Q,'L) tree_automaton \<Rightarrow> bool" where
  "is_tree_automaton automaton = (\<forall> s :: 'Q fset . (\<forall> x :: 'L . ((transition automaton) s x) |\<in>| (state_set automaton)))"
  
  (*definition is_finite_tree_automaton :: "('Q,'L) tree_automaton \<Rightarrow> bool" where
   "is_finite_tree_automaton automaton = ((is_tree_automaton automaton))"
   (*"is_finite_tree_automaton automaton = ((is_tree_automaton automaton) \<and> (finite (state_set automaton)))"*)
*)
  
primrec evaluation where
  "(evaluation automaton) (NODE symbol1 fset2) = (((transition automaton) (fimage (evaluation automaton) fset2)) symbol1)"
  
definition
  preImage :: "('a => 'b) => 'b set => 'a set" where
  "preImage \<ff> y = { x . \<ff> x \<in> y}"
  
fun recognized_tree :: "('Q,'L) tree_automaton \<Rightarrow> 'Q set \<Rightarrow> 'L tree set \<Rightarrow> bool" where
  "recognized_tree automaton stateSet language = (preImage (evaluation automaton) stateSet = language)"  
  
  
fun regular_tree :: "'L tree set \<Rightarrow> bool" where
  "regular_tree language = (\<exists> automaton :: (nat,'L) tree_automaton . (is_tree_automaton automaton) \<and> (\<exists> stateSet . (recognized_tree automaton stateSet language)))"   
  
  
definition prefixLetter :: "abc \<Rightarrow> abc list set \<Rightarrow> abc list set" where
  "prefixLetter \<alpha> I = (\<lambda>x.(\<alpha>#x)) ` I"
  
abbreviation prefixLetterAbb :: "abc \<Rightarrow> abc list set \<Rightarrow> abc list set" (infixr "\<bullet>" 80) where "(x \<bullet> y) \<equiv> prefixLetter x y"
  
abbreviation fstAbb :: "'a \<times> 'b \<Rightarrow> 'a" ("\<pi>\<^sup>1" 1000) where "\<pi>\<^sup>1 x \<equiv> fst x"
abbreviation sndAbb :: "'a \<times> 'b \<Rightarrow> 'b" ("\<pi>\<^sup>2" 1000) where "\<pi>\<^sup>2 x \<equiv> snd x"
  
(*lemma hallo :
  assumes "l1 \<subseteq> l2"
  assumes "\<And>x. \<pi>\<^sup>1 x = y"
  shows "\<alpha> \<bullet> l1 \<subseteq> \<alpha> \<bullet> l2"
  using assms prefixLetter_def by auto*)
    
  
  
  (* --------------------------------------------------------- *)
  (*  FACTORS OF FOREST LANGUAGES  *)
  (* --------------------------------------------------------- *)
    
lemma prefixLetterMono :
  assumes "l1 \<subseteq> l2"
  shows "\<alpha> \<bullet> l1 \<subseteq> \<alpha> \<bullet> l2"
  using assms prefixLetter_def by auto
    
definition factorByRootSymbol :: "abc \<Rightarrow> abc tree set \<Rightarrow> abc tree set" where 
  "factorByRootSymbol symb language = {t. (\<exists>tree \<in> language . (root tree = symb \<and> t |\<in>| childrenSet tree))}"
  
definition factorByRootSymbolF :: "abc \<Rightarrow> abc tree fset \<Rightarrow> abc tree fset" where 
  "factorByRootSymbolF symb language = set_to_fset {t. (\<exists>tree . tree |\<in>| language \<and> (root tree = symb \<and> t |\<in>| childrenSet tree))}"
  
abbreviation factorByRootSymbolFAbb :: "abc \<Rightarrow> abc tree fset \<Rightarrow> abc tree fset" (infixr "\<diamondop>" 80) where "(x \<diamondop> y) \<equiv> factorByRootSymbolF x y"
  
abbreviation factorByRootSymbolAbb :: "abc \<Rightarrow> abc tree set \<Rightarrow> abc tree set" (infixr "\<diamondop>\<tau>\<lambda>" 80) where "(x \<diamondop>\<tau>\<lambda> y) \<equiv> factorByRootSymbol x y"
  
  
  (* --------------------------------------------------------- *)
  (*  TREES AND PATHSETS  *)
  (* --------------------------------------------------------- *)
section "Trees"
  
primrec height :: "abc tree \<Rightarrow> nat" where
  "height (NODE symb2 set2) = 1 + (maxFset (fimage height set2))" 
  
  (*lemma is_measure_size [measure_function]: "is_measure height"
  by (simp add: is_measure_trivial)*)
  
  
  
definition topRule :: "('Q,'L) tree_automaton \<Rightarrow> 'L tree \<Rightarrow> ('Q,'L) rule" where
  "topRule automaton tr = rule.make (fimage (evaluation automaton) (childrenSet tr)) (root tr)"
  
  
  
primrec \<Pi> :: "'L tree \<Rightarrow> 'L list fset" where
  "\<Pi> (NODE symb2 set2) = fimage (append [symb2]) ((\<Union>| (fimage \<Pi> set2)) |\<union>|  (finsert [] {||})) "
  
lemma pathAlternateDef :
    "\<Pi> (NODE symb2 set2) = fimage (\<lambda> tail.(symb2#tail)) ((\<Union>| (fimage \<Pi> set2)) |\<union>|  (finsert [] {||})) "
  using \<Pi>.simps by auto
    
  
lemma noEmptyPathsInPi :
  assumes "a |\<in>| \<Pi> tr"
  obtains y where "a = (root tr)#y"
  using pathAlternateDef    by (metis assms childrenSet.elims fimageE root.simps)
    
  
lemma rootIsPath :
  "[symb] |\<in>| \<Pi> (NODE symb set2)"
proof -
  have "[] |\<in>| ((\<Union>| (fimage \<Pi> set2)) |\<union>|  (finsert [] {||}))" by blast
  then have "[symb]  |\<in>| fimage (append [symb]) ((\<Union>| (fimage \<Pi> set2)) |\<union>|  (finsert [] {||})) " by blast
  then show ?thesis using \<Pi>_def by simp
qed
  
  lemma rootIsPath2 :
  "[root tree] |\<in>| \<Pi> tree"
using rootIsPath root.simps   by (metis tree.exhaust) 
  
    
  
  
lemma pathsEq : "\<Pi> (NODE symb2 set2) = fimage (\<lambda> x. symb2#x) (\<Union>| (fimage \<Pi> set2) |\<union>|  (finsert [] {||}))" using \<Pi>.simps by auto
    
lemma paths_def : "tail |\<in>| \<Pi> child \<Longrightarrow> child |\<in>| set2 \<Longrightarrow> \<alpha>#tail |\<in>| \<Pi> (NODE \<alpha> set2)" using pathsEq  by (simp add: rev_fBexI) 
    
    (*termination
proof -
fix z :: "'L tree"
fix set2 :: "'L tree fset"
fix symb2 :: "'L"
assume 1 : "z \<in> fset set2"
from 1 children_smaller_depth have "Suc (height z) \<le> ( height (NODE symb2 set2))" by blast
from this have "height z < Suc (ffold max 0 (height |`| set2))" by blast*)
    (* \<And> set2 z. z \<in> fset set2 \<Longrightarrow> height z < Suc (ffold max 0 (height |`| set2)*)
    
    
definition pathsInForest :: "'L tree fset \<Rightarrow> 'L list fset" where
  "pathsInForest forest = \<Union>| (\<Pi> |`| forest)"
  
lemma pathsTreeForest :
  fixes p
  shows "(p |\<in>| pathsInForest f) = (\<exists> tr. (tr |\<in>| f \<and> p |\<in>| \<Pi> tr))"
proof -
  have "(p |\<in>|  \<Union>| (\<Pi> |`| f)) = (\<exists> trset . (p |\<in>| trset \<and>  trset |\<in>| (\<Pi> |`| f)))" by auto
  then show ?thesis        using pathsInForest_def by fastforce
qed
  
  
  
abbreviation deltaF :: "abc tree fset \<Rightarrow> abc list fset" ("\<delta>\<^sub>\<phi>") where "\<delta>\<^sub>\<phi> x \<equiv> pathsInForest x"
abbreviation deltaT :: "abc tree \<Rightarrow> abc list fset" ("\<delta>\<^sub>\<tau>") where "\<delta>\<^sub>\<tau> x \<equiv> \<Pi> x"
abbreviation deltaFL :: "abc tree fset set \<Rightarrow> abc list fset set" ("\<delta>\<^sub>\<phi>\<^sub>\<lambda>") where "\<delta>\<^sub>\<phi>\<^sub>\<lambda> x \<equiv> \<delta>\<^sub>\<phi> ` x"
abbreviation deltaTL :: "abc tree set \<Rightarrow> abc list fset set" ("\<delta>\<^sub>\<tau>\<^sub>\<lambda>") where "\<delta>\<^sub>\<tau>\<^sub>\<lambda> x \<equiv> \<delta>\<^sub>\<tau> ` x"
  
definition pathsForForestLanguage :: "'L tree fset set \<Rightarrow> 'L list set" where
  "pathsForForestLanguage language = {p . (\<exists> t \<in> language . p |\<in>| pathsInForest t)}"
  
definition pathsForTreeLanguage :: "'L tree set \<Rightarrow> 'L list set" where
  "pathsForTreeLanguage language = {p . (\<exists> t \<in> language . p |\<in>| \<Pi> t)}" (* ((Union :: ('L list fset set \<Rightarrow> 'L list set)) (image \<Pi> language))"*)
  
abbreviation "\<Pi>\<^sub>\<iota>\<^sub>\<phi>" :: "'L tree fset \<Rightarrow> 'L list fset" ("\<Pi>\<^sub>\<iota>\<^sub>\<phi>") where "\<Pi>\<^sub>\<iota>\<^sub>\<phi> \<equiv> pathsInForest"
  
abbreviation "\<Pi>\<^sub>\<phi>" :: "'L tree fset set \<Rightarrow> 'L list set" ("\<Pi>\<^sub>\<phi>") where "\<Pi>\<^sub>\<phi> \<equiv> pathsForForestLanguage"
abbreviation "\<Pi>\<^sub>\<tau>" :: "'L tree set \<Rightarrow> 'L list set" ("\<Pi>\<^sub>\<tau>") where "\<Pi>\<^sub>\<tau> \<equiv> pathsForTreeLanguage"
  
abbreviation "\<Pi>\<^sub>\<tau>\<^sub>F" :: "'L tree fset \<Rightarrow> 'L list set" ("\<Pi>\<^sub>\<tau>\<^sub>F") where "\<Pi>\<^sub>\<tau>\<^sub>F x \<equiv> pathsForTreeLanguage (fset x)"  
  
abbreviation "\<Pi>\<^sub>\<delta>" :: "'L list fset set \<Rightarrow> 'L list set" ("\<Pi>\<^sub>\<delta>") where "\<Pi>\<^sub>\<delta> x \<equiv> \<Union> (fset ` x)"
  
  
  
abbreviation "bounded"  :: "nat \<Rightarrow> abc tree fset" where "bounded n \<equiv> Abs_fset {f . height f \<le> n}"
  
abbreviation "boundedForests"  :: "nat \<Rightarrow> abc tree fset fset" where "boundedForests n \<equiv> Abs_fset {f . (\<forall> t . t |\<in>| f \<longrightarrow> height t \<le> n)}"
  
  
  (* For each n, there are only finitely many trees of height \<le> n *)
lemma restrictionIsFinite:
  fixes n
  shows "fset (bounded n) = {(f :: abc tree) . height f \<le> n}"
proof (induct n)
  case 0
  have "\<And>f. \<not> (height f \<le> 0)" using height.simps        by (metis add_eq_0_iff_both_eq_0 childrenSet.cases le_zero_eq not_one_le_zero) 
  then have "{f . height f \<le> 0} = {}"          by blast 
  then show ?case by (metis (no_types)  bot_fset.rep_eq bot_fset_def)
next
  case (Suc n)
  assume b1 : "fset (bounded n) = {f. height f \<le> n}"
  def smaller_set == "{(f :: abc tree). height f \<le> n}"
  then have n76 : "fset (bounded n) = smaller_set" using b1 by simp
  have w1 : "finite {f. height f = Suc n}"
  proof -
    have "\<And>f . (height f = Suc n \<Longrightarrow> (f |\<in>| (\<Union>| ((\<lambda> alpha. ((\<lambda> x.(NODE alpha x)) |`| fPow (bounded n))) |`| (Abs_fset (UNIV :: abc set))))))"
    proof -
      fix f :: "abc tree"
      assume k76789 : "height f = Suc n"
      have "((height f = Suc n) = (Suc n = 1 + (maxFset (fimage height (childrenSet f)))))" using height.simps           by (metis childrenSet.elims) 
      also have u1 : "(... = (n = (maxFset (fimage height (childrenSet f)))))"           by auto
      have u5678 : "Rep_abc ` (UNIV :: abc set) = {n . n \<le> numberOfLettersAndStates}"            using type_definition.Rep_range type_definition_abc by blast
      have u5678b : "finite {n . n \<le> numberOfLettersAndStates}"           by simp
      from u5678 u5678b have "finite (Rep_abc ` (UNIV :: abc set))"            by simp
      then have n5456 : "finite ( (UNIV :: abc set))"                by (metis (full_types) Rep_abc_inverse UNIV_I ex_new_if_finite finite_imageI image_eqI)
      have n767890 : "(height f = Suc n \<Longrightarrow> ((childrenSet f) |\<in>| fPow (bounded n)))"
      proof 
        assume "(height f = Suc n)"
        then have n1 : "(n = (maxFset (fimage height (childrenSet f))))" using u1 calculation by auto 
        show "childrenSet f |\<subseteq>| (bounded n)"
        proof 
          fix child
          assume m1 : "child |\<in>| childrenSet f"
          from n1 m1 have "height child \<le> n"                     by (simp add: finiteMaxExists)
          then have "child \<in> {f . height f \<le> n}" using m1 by blast
          then have "child \<in> smaller_set" using smaller_set_def by simp
          then have "child \<in> (fset (bounded n))" using b1 n76 by simp
          then show "child |\<in>| ((bounded n))" using notin_fset by metis
        qed
      qed
      have n56568 : "(height f = Suc n \<Longrightarrow> (f |\<in>| ((\<lambda> x.(NODE (root f) x)) |`| fPow (bounded n))))"
      proof
        show "f = NODE (root f) (childrenSet f)" using childrenSet.simps childrenSet.elims            by (metis root.simps) 
        show "height f = Suc n  \<Longrightarrow> childrenSet f |\<in>| fPow (bounded n)"   using n767890 by auto
      qed
      show "f |\<in>| (\<Union>| ((\<lambda> alpha. ((\<lambda> x.(NODE alpha x)) |`| fPow (bounded n))) |`| (Abs_fset (UNIV :: abc set))))"
      proof -
        from n56568 k76789 obtain alpha where b7 : "(f |\<in>| ((\<lambda> x.(NODE alpha x)) |`| fPow (bounded n)))" by auto
        have b8 : "alpha |\<in>| (Abs_fset (UNIV :: abc set))" using n5456                 by (metis UNIV_I fset_inverse fset_to_fset notin_fset) 
        from b7 b8 show "f |\<in>| (\<Union>| ((\<lambda> alpha. ((\<lambda> x.(NODE alpha x)) |`| fPow (bounded n))) |`| (Abs_fset (UNIV :: abc set))))" by auto
      qed
    qed
    then have "{f. height f = Suc n} \<subseteq> (fset (\<Union>| ((\<lambda> alpha. ((\<lambda> x.(NODE alpha x)) |`| fPow (bounded n))) |`| (Abs_fset (UNIV :: abc set)))))"               by (metis (mono_tags, lifting) mem_Collect_eq notin_fset subsetI)
    then show "finite {f. height f = Suc n}"                  using finite_fset infinite_super by blast
  qed
  have w2 : "{f. height f \<le> Suc n} = {f. height f \<le> n} \<union> {f. height f = Suc n}"      by auto
  from b1 have w3 : "finite {f. height f \<le> n}"      by (metis finite_fset) 
  from w1 w2 w3 have "finite {f. height (f :: abc tree) \<le> Suc n}" by auto
  then show "fset (bounded (Suc n)) = {f. height f \<le> Suc n}"      by (simp add: Abs_fset_inverse) 
qed
  
  
  
lemma restrictionIsFinite2:
  fixes n
  shows "\<And> p . (p |\<in>| (bounded n)) = (height p \<le> n)"
  using restrictionIsFinite  by (metis (full_types) mem_Collect_eq notin_fset)
    
    
    
lemma restrictionIsFiniteForests:
  fixes n
  shows "fset (boundedForests n) = {f . (\<forall> t . t |\<in>| f \<longrightarrow> height t \<le> n)}"
proof -
  have a1 : "\<And> p. ((p |\<in>| fPow (bounded n)) = (\<forall> t . t |\<in>| p \<longrightarrow> height t \<le> n))" using restrictionIsFinite2    by blast 
  then have a10 : "(fset ( fPow (bounded n))) = {f . (\<forall> t . t |\<in>| f \<longrightarrow> height t \<le> n)}" 
  proof -
    from a1 have "\<And>p . ((p \<in> (fset ( fPow (bounded n)))) =  (\<forall> t . t |\<in>| p \<longrightarrow> height t \<le> n))" using notin_fset by metis
    then have "\<And>p . ((p \<in> (fset ( fPow (bounded n)))) = (p \<in> {f . (\<forall> t . t |\<in>| f \<longrightarrow> height t \<le> n)}))" by blast
    then show "(fset ( fPow (bounded n))) = {f . (\<forall> t . t |\<in>| f \<longrightarrow> height t \<le> n)}" using set_eqI by blast
  qed
  then    have "Abs_fset (fset ( fPow (bounded n))) = Abs_fset {f . (\<forall> t . t |\<in>| f \<longrightarrow> height t \<le> n)}"  by (simp add: \<open>fset (fPow (bounded n)) = {f. \<forall>t. t |\<in>| f \<longrightarrow> height t \<le> n}\<close>) 
  then have "( ( fPow (bounded n))) = Abs_fset {f . (\<forall> t . t |\<in>| f \<longrightarrow> height t \<le> n)}"  by (simp add: fset_inverse)  
  then have "fset (Abs_fset {f . (\<forall> t . t |\<in>| f \<longrightarrow> height t \<le> n)}) = {f . (\<forall> t . t |\<in>| f \<longrightarrow> height t \<le> n)}" using a10    by (simp add: \<open>fPow (bounded n) = boundedForests n\<close>) 
  then show "fset (boundedForests n) = {f . (\<forall> t . t |\<in>| f \<longrightarrow> height t \<le> n)}" by auto
qed
  
  
definition Z :: "nat \<Rightarrow> abc tree set \<Rightarrow> abc tree set" where
  "Z n L = { \<ff> . ((\<ff> \<in> L) \<and> (height \<ff> \<le> n))}"
  
definition \<Z>\<^sub>\<tau> :: "nat \<Rightarrow> abc tree set \<Rightarrow> abc tree fset" where
  "\<Z>\<^sub>\<tau> n L = inf_fset2 (bounded n) L" (*(SOME x. fset x = { \<ff> . ((\<ff> \<in> L) \<and> (height \<ff> \<le> n))})"   *)
  
lemma \<Z>\<tau>_lemma : "fset (\<Z>\<^sub>\<tau> nm l1) = Z nm l1" using restrictionIsFinite inf_fset2_def
  by (metis Collect_conj_eq Collect_mem_eq Int_commute Z_def \<Z>\<^sub>\<tau>_def inf_fset2.rep_eq) 
    
lemma \<Z>\<tau>_subset : "fset (\<Z>\<^sub>\<tau> n l) \<subseteq> l" using \<Z>\<tau>_lemma
  using \<Z>\<^sub>\<tau>_def inf_fset2.rep_eq by fastforce
    
definition \<Z>\<^sub>\<delta> :: "nat \<Rightarrow> abc list fset set \<Rightarrow> abc list fset fset" where
  "\<Z>\<^sub>\<delta> n L = \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| (inf_fset2 (boundedForests n) {f . (\<Pi>\<^sub>\<iota>\<^sub>\<phi> f \<in> L)} )"
  
  
definition \<Z>\<^sub>\<phi> :: "nat \<Rightarrow> abc tree fset set \<Rightarrow> abc tree fset fset" where
  "\<Z>\<^sub>\<phi> n L = inf_fset2 (boundedForests n) L" (*(SOME x. fset x = { \<ff> . ((\<ff> \<in> L) \<and> (\<forall> t. t|\<in>| \<ff> \<longrightarrow> (height t \<le> n)))})"   *)
definition \<Z>\<^sub>\<phi>\<^sub>F :: "nat \<Rightarrow> abc tree fset set \<Rightarrow> abc tree fset set" where
  "\<Z>\<^sub>\<phi>\<^sub>F n L = L \<inter> {f . (\<forall> t . t |\<in>| f \<longrightarrow> height t \<le> n)}"  
  
lemma \<Z>\<^sub>\<phi>\<Z>\<^sub>\<phi>\<^sub>Flemma :
  shows "\<Z>\<^sub>\<phi>\<^sub>F n L = fset (\<Z>\<^sub>\<phi> n L)"
  by (simp add: restrictionIsFiniteForests Int_commute \<Z>\<^sub>\<phi>\<^sub>F_def \<Z>\<^sub>\<phi>_def inf_fset2.rep_eq)
    
    
lemma \<Z>\<^sub>\<phi>\<^sub>F_subset : "\<Z>\<^sub>\<phi>\<^sub>F n lang \<subseteq> lang" using \<Z>\<^sub>\<phi>\<^sub>F_def by blast
    
lemma aux50 : "\<And> x . \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n x) = \<Pi>\<^sub>\<tau>\<^sub>F ((\<Union>| (\<Z>\<^sub>\<phi> n x)))"
proof -
  fix x
  have "\<And>p . p \<in> \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n x) = (p \<in> {p . (\<exists> t \<in> (\<Z>\<^sub>\<phi>\<^sub>F n x) . p |\<in>| pathsInForest t)})" using pathsForForestLanguage_def by auto
  then have k10 : "\<And>p . p \<in> \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n x) = (\<exists> t \<in> (\<Z>\<^sub>\<phi>\<^sub>F n x) . p |\<in>| pathsInForest t)" by blast
  have "\<And>p. (p \<in> \<Pi>\<^sub>\<tau>\<^sub>F ((\<Union>| (\<Z>\<^sub>\<phi> n x)))) = (p \<in> {p . (\<exists> t \<in>  (fset (\<Union>| (\<Z>\<^sub>\<phi> n x))     )     . p |\<in>| \<Pi> t)})" using pathsForTreeLanguage_def by blast
  then have "\<And>p. (p \<in> \<Pi>\<^sub>\<tau>\<^sub>F ((\<Union>| (\<Z>\<^sub>\<phi> n x)))) = (\<exists> t \<in>  (fset (\<Union>| (\<Z>\<^sub>\<phi> n x))     )     . p |\<in>| \<Pi> t)" by blast
  then have "\<And>p. (p \<in> \<Pi>\<^sub>\<tau>\<^sub>F ((\<Union>| (\<Z>\<^sub>\<phi> n x)))) = (\<exists> t. (t |\<in>|  ( (\<Union>| (\<Z>\<^sub>\<phi> n x))     )     \<and> p |\<in>| \<Pi> t))"        by (meson notin_fset) 
  then have "\<And>p. (p \<in> \<Pi>\<^sub>\<tau>\<^sub>F ((\<Union>| (\<Z>\<^sub>\<phi> n x)))) = (\<exists> t. (t |\<in>|  ( (\<Union>| (inf_fset2 (boundedForests n) x))     )     \<and> p |\<in>| \<Pi> t))"  using \<Z>\<^sub>\<phi>_def          by (simp add: \<Z>\<^sub>\<phi>_def)
  then have "\<And>p. (p \<in> \<Pi>\<^sub>\<tau>\<^sub>F ((\<Union>| (\<Z>\<^sub>\<phi> n x)))) = (\<exists> t. (\<exists> for . (t |\<in>| for \<and> for |\<in>| (inf_fset2 (boundedForests n) x))     )     \<and> p |\<in>| \<Pi> t)"    by auto
  then have a1 : "\<And>p. (p \<in> \<Pi>\<^sub>\<tau>\<^sub>F ((\<Union>| (\<Z>\<^sub>\<phi> n x)))) = (\<exists> t. (\<exists> for . (t |\<in>| for \<and> for \<in> (\<Z>\<^sub>\<phi>\<^sub>F n x))     )     \<and> p |\<in>| \<Pi> t)" using \<Z>\<^sub>\<phi>\<Z>\<^sub>\<phi>\<^sub>Flemma        by (smt \<open>\<And>p. (p \<in> \<Pi>\<^sub>\<tau>\<^sub>F (\<Union>| (\<Z>\<^sub>\<phi> n x))) = (\<exists>t. t |\<in>| \<Union>| (\<Z>\<^sub>\<phi> n x) \<and> p |\<in>| \<Pi> t)\<close> ffUnionI ffUnionLemma notin_fset) 
  from pathsInForest_def   have q5678 : "\<And>p t. ((p |\<in>| pathsInForest t) = (\<exists> tr. (tr |\<in>| t   \<and> p |\<in>| \<Pi> tr)))" by auto
  then have "\<And>p. (\<exists> t. (\<exists> for . (t |\<in>| for \<and> for \<in> (\<Z>\<^sub>\<phi>\<^sub>F n x))     )     \<and> p |\<in>| \<Pi> t) = (\<exists> t. (\<exists> for . (t |\<in>| for \<and> for \<in> (\<Z>\<^sub>\<phi>\<^sub>F n x) \<and> p |\<in>| pathsInForest for     )))"    by blast
  then have i6778 : "\<And>p. (p \<in> \<Pi>\<^sub>\<tau>\<^sub>F ((\<Union>| (\<Z>\<^sub>\<phi> n x)))) = (\<exists> t. (\<exists> for . (t |\<in>| for \<and> for \<in> (\<Z>\<^sub>\<phi>\<^sub>F n x) \<and> p |\<in>| pathsInForest for     )))" using a1 by auto
  have "\<And>p. (\<exists> t. (\<exists> for . (t |\<in>| for \<and> for \<in> (\<Z>\<^sub>\<phi>\<^sub>F n x) \<and> p |\<in>| pathsInForest for     ))) = ( (\<exists> for . (for \<in> (\<Z>\<^sub>\<phi>\<^sub>F n x) \<and> p |\<in>| pathsInForest for     )))" using q5678 by blast
  then have "\<And>p. (p \<in> \<Pi>\<^sub>\<tau>\<^sub>F ((\<Union>| (\<Z>\<^sub>\<phi> n x)))) = ( (\<exists> for . (for \<in> (\<Z>\<^sub>\<phi>\<^sub>F n x) \<and> p |\<in>| pathsInForest for     )))" using i6778 by auto
  then have "\<And>p . p \<in> \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n x) = (p \<in> \<Pi>\<^sub>\<tau>\<^sub>F ((\<Union>| (\<Z>\<^sub>\<phi> n x))))" using k10 by auto
  then show "\<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n x) = \<Pi>\<^sub>\<tau>\<^sub>F ((\<Union>| (\<Z>\<^sub>\<phi> n x)))" by auto
qed
  
section "Some basic concepts"
  
definition tree_for_rule :: "('Q,'L) tree_automaton \<Rightarrow> ('Q,'L) rule \<Rightarrow> 'L tree \<Rightarrow> bool" where
  "(tree_for_rule automaton rule1 tree1) = ((root tree1 = symbol rule1) \<and> ((fimage (((evaluation automaton))) (childrenSet tree1)) = states rule1))"
  
definition language_for_rule :: "('Q, 'L) tree_automaton \<Rightarrow> ('Q,'L) rule \<Rightarrow> (('L tree) set)" where
  "language_for_rule automaton rule = {tree . tree_for_rule automaton rule tree}"
  
  (* the empty forest cannot satisfy any rule *)
definition forest_language_for_rule :: "('Q, 'L) tree_automaton \<Rightarrow> ('Q,'L) rule \<Rightarrow> (('L tree fset) set)" where
  "forest_language_for_rule automaton rule = {forest . (\<forall>tree.(tree|\<in>|forest \<longrightarrow>  tree_for_rule automaton rule tree)) \<and> (\<exists> tree. tree |\<in>| forest)}"
  
definition language_for_state :: "('Q, 'L) tree_automaton \<Rightarrow> 'Q \<Rightarrow> (('L tree) set)" where
  "language_for_state automaton state = {tree . evaluation automaton tree = state}"
  
definition forest_language_for_state :: "('Q, 'L) tree_automaton \<Rightarrow> 'Q \<Rightarrow> (('L tree fset) set)" where
  "forest_language_for_state automaton state = {forest . (\<forall>tree.(tree|\<in>|forest \<longrightarrow> evaluation automaton tree = state)) \<and> (\<exists> tree. tree |\<in>| forest)}"
  
abbreviation "\<L>\<^sub>\<phi>\<^sub>\<sigma>" :: "('Q, 'L) tree_automaton \<Rightarrow> 'Q \<Rightarrow> (('L tree fset) set)" ("\<L>\<^sub>\<phi>\<^sub>\<sigma>") where "\<L>\<^sub>\<phi>\<^sub>\<sigma> \<equiv> forest_language_for_state"
abbreviation "\<L>\<^sub>\<tau>\<^sub>\<sigma>" :: "('Q, 'L) tree_automaton \<Rightarrow> 'Q \<Rightarrow> (('L tree) set)" ("\<L>\<^sub>\<tau>\<^sub>\<sigma>") where "\<L>\<^sub>\<tau>\<^sub>\<sigma> \<equiv> language_for_state"
abbreviation "\<L>\<^sub>\<phi>\<^sub>\<rho>" :: "('Q, 'L) tree_automaton \<Rightarrow> ('Q,'L) rule \<Rightarrow> (('L tree fset) set)" ("\<L>\<^sub>\<phi>\<^sub>\<rho>") where "\<L>\<^sub>\<phi>\<^sub>\<rho> \<equiv> forest_language_for_rule"
abbreviation "\<L>\<^sub>\<tau>\<^sub>\<rho>" :: "('Q, 'L) tree_automaton \<Rightarrow> ('Q,'L) rule \<Rightarrow> (('L tree) set)" ("\<L>\<^sub>\<tau>\<^sub>\<rho>") where "\<L>\<^sub>\<tau>\<^sub>\<rho> \<equiv> language_for_rule"
  
  
  
abbreviation "\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma>" ("\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma>") where "\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> x \<equiv>  \<delta>\<^sub>\<phi>\<^sub>\<lambda> \<circ> \<L>\<^sub>\<phi>\<^sub>\<sigma> x"
abbreviation "\<delta>\<L>\<^sub>\<phi>\<^sub>\<rho>" ("\<delta>\<L>\<^sub>\<phi>\<^sub>\<rho>") where "\<delta>\<L>\<^sub>\<phi>\<^sub>\<rho> x \<equiv>  \<delta>\<^sub>\<phi>\<^sub>\<lambda> \<circ> \<L>\<^sub>\<phi>\<^sub>\<rho> x"
abbreviation "\<delta>\<L>\<^sub>\<tau>\<^sub>\<sigma>" ("\<delta>\<L>\<^sub>\<tau>\<^sub>\<sigma>") where "\<delta>\<L>\<^sub>\<tau>\<^sub>\<sigma> x \<equiv>  \<delta>\<^sub>\<tau>\<^sub>\<lambda> \<circ> \<L>\<^sub>\<tau>\<^sub>\<sigma> x"
abbreviation "\<delta>\<L>\<^sub>\<tau>\<^sub>\<rho>" ("\<delta>\<L>\<^sub>\<tau>\<^sub>\<rho>") where "\<delta>\<L>\<^sub>\<tau>\<^sub>\<rho> x \<equiv>  \<delta>\<^sub>\<tau>\<^sub>\<lambda> \<circ> \<L>\<^sub>\<tau>\<^sub>\<rho> x"
  
definition evalRule :: "('Q,'L) tree_automaton \<Rightarrow> ('Q,'L) rule \<Rightarrow> 'Q" where
  "evalRule automaton rule = transition automaton (states rule) (symbol rule)" 
  
  
  
definition childrenWithSymbol where "childrenWithSymbol symbol2 set2 = inf_fset2 set2 {child1 . (root child1 = symbol2)}"
  
  
definition plus :: "'L tree fset \<Rightarrow> 'L tree fset \<Rightarrow> 'L tree fset" where
  "plus f1 f2 = f1 |\<union>| f2"   
  
  (*fun plus :: "'L tree \<Rightarrow> 'L tree \<Rightarrow> 'L tree" where
   "plus (NODE s1 c1) (NODE s2 c2) = (NODE s1 (c1 |\<union>| c2))"*)
  
  (*definition oplus :: "'L tree \<Rightarrow> 'L tree \<Rightarrow> 'L tree" where
   "oplus t1 t2 =  psi (plus t1 t2)"*)
  
definition plusl :: "'L tree fset set \<Rightarrow> 'L tree fset set \<Rightarrow> 'L tree fset set" where
  "plusl l1 l2 = {tr . (\<exists> t1 \<in> l1. (\<exists> t2 \<in> l2. (tr = t1 |\<union>| t2)))}"
  
definition uplus :: "'L tree fset set \<Rightarrow> 'L tree fset set \<Rightarrow> 'L tree fset set" where
  "(uplus l1 l2) = (l1 \<union> (l2 \<union> (plusl l1 l2)))"
  
  
definition plusD :: "'L list fset \<Rightarrow> 'L list fset \<Rightarrow> 'L list fset" where
  "plusD f1 f2 = f1 |\<union>| f2"   
  
  (*fun plus :: "'L tree \<Rightarrow> 'L tree \<Rightarrow> 'L tree" where
   "plus (NODE s1 c1) (NODE s2 c2) = (NODE s1 (c1 |\<union>| c2))"*)
  
  (*definition oplus :: "'L tree \<Rightarrow> 'L tree \<Rightarrow> 'L tree" where
   "oplus t1 t2 =  psi (plus t1 t2)"*)
  
definition pluslD :: "'L list fset set \<Rightarrow> 'L list fset set \<Rightarrow> 'L list fset set" where
  "pluslD l1 l2 = {tr . (\<exists> t1 \<in> l1. (\<exists> t2 \<in> l2. (tr = t1 |\<union>| t2)))}"
  
definition uplusD :: "'L list fset set \<Rightarrow> 'L list fset set \<Rightarrow> 'L list fset set" where
  "(uplusD l1 l2) = (l1 \<union> (l2 \<union> (pluslD l1 l2)))"   
  
  
  
  
definition realizedIn :: "'L tree set \<Rightarrow> 'L list set \<Rightarrow> bool" where
  "realizedIn l \<ff> = (\<exists>\<gg> . ((\<gg> \<in> l) \<and> (fset (\<Pi> \<gg>) \<subseteq> \<ff>)))"
  
definition realizedInForest :: "'L tree fset set \<Rightarrow> 'L list set \<Rightarrow> bool" where
  "realizedInForest l \<ff> = (\<exists>\<gg> . ((\<gg> \<in> l) \<and> (fset (pathsInForest  \<gg>) \<subseteq> \<ff>)))"
  
  
definition realizedInD :: "'L list fset set \<Rightarrow> 'L list set \<Rightarrow> bool" where
  "realizedInD l \<ff> = (\<exists>\<gg> . ((\<gg> \<in> l) \<and> ((fset \<gg>) \<subseteq> \<ff>)))"
  
  
  
  
  (* ============================================= *)
section "Introducing fixed constants for the separation proof"
  
  
definition \<A>\<^sub>1 :: "(stt,abc) tree_automaton" where
  "\<A>\<^sub>1 = Eps(is_tree_automaton)"
definition \<A>\<^sub>2 :: "(stt,abc) tree_automaton" where
  "\<A>\<^sub>2 = Eps(\<lambda>x.(is_tree_automaton x \<and> x \<noteq> \<A>\<^sub>1))"
  (* TODO needs to say that this is about psi *)
fun \<A> :: "ot \<Rightarrow> (stt,abc) tree_automaton" where
  "\<A> \<aa>\<^sub>1 = \<A>\<^sub>1"
| "\<A> \<aa>\<^sub>2 = \<A>\<^sub>2"
lemma aut_def : "\<A>\<^sub>1 = \<A> \<aa>\<^sub>1 \<and> \<A>\<^sub>2 = \<A> \<aa>\<^sub>2"
  by simp 
    
    
definition rules_of_state :: "('Q,'L) tree_automaton \<Rightarrow> 'Q \<Rightarrow> ('Q,'L) rule set" where
  "rules_of_state automaton state = {r . evalRule automaton r = state}"
definition rulesForState :: "ot \<Rightarrow> stt \<Rightarrow> (stt,abc) rule fset" where
  "(rulesForState \<ii> sta) = (ffilter (\<lambda>r. transition (\<A> \<ii>) (states r) (symbol r) = sta) (rule_set (\<A> \<ii>)))"
  
  
  

  (* ============================================= *)
section "Upper Bound N"
  
definition existential_satisfaction_set :: "'L list set \<Rightarrow> 'L tree set" where
  "existential_satisfaction_set i = {t . (\<exists> x . x \<in> ((fset (\<Pi> t)) \<inter> i))}"
  
definition existential_satisfaction_setForest :: "'L list set \<Rightarrow> 'L tree fset set" where
  "existential_satisfaction_setForest i = {t . (\<exists> x . x \<in> ((fset (pathsInForest  t)) \<inter> i))}"
  
definition entails :: "'L tree set \<Rightarrow> 'L list set \<Rightarrow> bool" where
  "entails l i 
     = (l \<subseteq> (existential_satisfaction_set i))"    
  
abbreviation entailsAbb :: "'L tree set \<Rightarrow> 'L list set \<Rightarrow> bool" (infixr "\<Turnstile>" 80) where "(x \<Turnstile> y) \<equiv> entails x y"
  
definition entailsForest :: "'L tree fset set \<Rightarrow> 'L list set \<Rightarrow> bool" where
  "entailsForest l i 
     = (l \<subseteq> (existential_satisfaction_setForest i))"    
  
  
lemma entails_altdef :
  fixes l
  fixes I
  shows "l \<Turnstile> I = (\<forall>x \<in> l.((fset (\<Pi> x)) \<inter> I \<noteq> {}))"
  by (smt IntI disjoint_iff_not_equal emptyE entails_def existential_satisfaction_set_def mem_Collect_eq subsetCE subsetI) 
    
    
    
definition emptyForest :: "'L tree fset" where
  "emptyForest = fempty"
  
  
  
definition distEquivalenceClassForests :: "'L tree fset set \<Rightarrow> 'L tree fset set" where
  "distEquivalenceClassForests lang = {forest . (\<exists> forest2 \<in> lang. pathsInForest forest = pathsInForest forest2)}"
  
definition biguplusForests :: "'L tree fset set fset \<Rightarrow> 'L tree fset set" where
  "biguplusForests languages = {(forest :: 'L tree fset) . (\<forall> (tr :: 'L tree) . tr |\<in>| forest \<longrightarrow> (\<exists> lang . lang |\<in>| languages \<and> (\<exists> (subforest :: 'L tree fset) . (tr |\<in>| subforest \<and> subforest |\<subseteq>| forest \<and> subforest \<in> lang)))) }"
definition biguplusForestsD :: "'L list fset set fset \<Rightarrow> 'L list fset set" where
  "biguplusForestsD languages = {(forest :: 'L list fset) . (\<forall> (tr :: 'L list) . tr |\<in>| forest \<longrightarrow> (\<exists> lang . lang |\<in>| languages \<and> (\<exists> (subforest :: 'L list fset) . (tr |\<in>| subforest \<and> subforest |\<subseteq>| forest \<and> subforest \<in> lang)))) }"
  
abbreviation biguplusForestsAbb :: "'L tree fset set fset \<Rightarrow> 'L tree fset set" ("\<Uplus>") where "\<Uplus> x \<equiv> biguplusForests x"
abbreviation biguplusForestsDAbb :: "'L list fset set fset \<Rightarrow> 'L list fset set" ("\<Uplus>\<^sub>\<delta>") where "\<Uplus>\<^sub>\<delta> x \<equiv> biguplusForestsD x"
  
definition bigoplusForests :: "'L tree fset set fset \<Rightarrow> 'L tree fset set" where
  "bigoplusForests languages = {(forest :: 'L tree fset) . forest \<in> (biguplusForests languages) \<and> (\<forall> lang . lang |\<in>| languages \<longrightarrow> (\<exists> subforest . (subforest \<in> lang \<and> subforest |\<subseteq>| forest))) }"
definition bigoplusForestsD :: "'L list fset set fset \<Rightarrow> 'L list fset set" where
  "bigoplusForestsD (languages :: 'L list fset set fset) = {(forest :: 'L list fset) . forest \<in> (biguplusForestsD languages) \<and> (\<forall> lang . lang |\<in>| languages \<longrightarrow> (\<exists> subforest . (subforest \<in> lang \<and> subforest |\<subseteq>| forest))) }"
  
abbreviation bigoplusForestsAbb :: "'L tree fset set fset \<Rightarrow> 'L tree fset set" ("\<Oplus>") where "\<Oplus> x \<equiv> bigoplusForests x"
abbreviation bigoplusForestsDAbb :: "'L list fset set fset \<Rightarrow> 'L list fset set" ("\<Oplus>\<^sub>\<delta>") where "\<Oplus>\<^sub>\<delta> x \<equiv> bigoplusForestsD x"
  
  
  lemma uplusInOplus :
  "\<Uplus> S1 \<supseteq> \<Oplus> S1"
  using bigoplusForests_def by blast
    
    
lemma uplusInOplusD :
  "\<Uplus>\<^sub>\<delta> S1 \<supseteq> \<Oplus>\<^sub>\<delta> S1"
  using bigoplusForestsD_def by auto
    
    
lemma realizedForestTreeRule :
  fixes r
  fixes \<ii>
  fixes pathset
  shows "realizedIn (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) r) pathset = realizedInForest  (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>) r) pathset"
proof
  {
    assume "realizedIn (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) r) pathset"
    from realizedIn_def obtain \<gg> where k1 : "((\<gg> \<in> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) r)) \<and> (fset (\<Pi> \<gg>) \<subseteq> pathset))" using \<open>realizedIn (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) r) pathset\<close> by blast
    from realizedInForest_def have  l2 : "realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>) r) pathset = (\<exists>\<gg> . ((\<gg> \<in> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>) r)) \<and> (fset (pathsInForest  \<gg>) \<subseteq> pathset)))" by auto
    def \<gg>F == "finsert \<gg> {||}"
    from k1 \<gg>F_def forest_language_for_rule_def have l3 : "\<gg>F \<in> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>) r)"       by (simp add: forest_language_for_rule_def language_for_rule_def) 
    from k1 \<gg>F_def pathsInForest_def pathsTreeForest have l1 : "(fset (pathsInForest  \<gg>F) \<subseteq> pathset)"          by (smt fsingleton_iff notin_fset subset_eq)
    from l1 l2 l3 show "realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>) r) pathset" by auto
  }
  {
    assume u1 : "realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>) r) pathset"
    from u1 realizedInForest_def obtain \<gg> where j2 : "((\<gg> \<in> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>) r)) \<and> (fset (pathsInForest  \<gg>) \<subseteq> pathset))" by blast
    then obtain tree where j1 : "((tree|\<in>|\<gg> \<and> tree_for_rule (\<A> \<ii>) r tree))" using forest_language_for_rule_def   mem_Collect_eq
      by smt
    from j2 j1 pathsInForest_def have j6 : "(fset (\<Pi> tree) \<subseteq> pathset)"              by (metis notin_fset pathsTreeForest set_mp subsetI)
    from j1 j6 have  "(\<exists>\<gg> . ((\<gg> \<in> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) r)) \<and> (fset (\<Pi> \<gg>) \<subseteq> pathset)))"      using language_for_rule_def by blast 
    then show "realizedIn (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) r) pathset" using realizedIn_def by auto
  }
qed
  
  
lemma pathsForestLangMonotone : "L1 \<subseteq> L2 \<Longrightarrow> \<Pi>\<^sub>\<phi> L1 \<subseteq> \<Pi>\<^sub>\<phi> L2" by (smt mem_Collect_eq pathsForForestLanguage_def subset_eq)
lemma pathsTreeLangMonotone : "L1 \<subseteq> L2 \<Longrightarrow> \<Pi>\<^sub>\<tau> L1 \<subseteq> \<Pi>\<^sub>\<tau> L2" by (smt mem_Collect_eq pathsForTreeLanguage_def subset_eq)
    
    
    
  
lemma realizedForestTreeState :
  fixes state
  fixes \<ii>
  fixes pathset
  shows "realizedIn (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> \<ii>) state) pathset = realizedInForest  (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>) state) pathset"
proof 
  from realizedIn_def have "realizedIn (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> \<ii>) state) pathset = (\<exists>\<gg> . ((\<gg> \<in> (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> \<ii>) state)) \<and> (fset (\<Pi> \<gg>) \<subseteq> pathset)))" by auto
  from realizedInForest_def have "realizedInForest  (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>) state) pathset = (\<exists>\<gg> . ((\<gg> \<in> (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>) state)) \<and> (fset (pathsInForest  \<gg>) \<subseteq> pathset)))" by auto
  from forest_language_for_state_def have  "\<And> \<gg>. ((\<gg> \<in> (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>) state)) =  ((\<forall>tree.(tree|\<in>|\<gg> \<longrightarrow> evaluation (\<A> \<ii>) tree = state)) \<and> (\<exists> tree. tree |\<in>| \<gg>)))"    by (simp add: forest_language_for_state_def)
  {
    assume "realizedIn (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> \<ii>) state) pathset"
    then obtain \<gg> where b1 : "(((\<gg> \<in> (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> \<ii>) state)) \<and> (fset (\<Pi> \<gg>) \<subseteq> pathset)))" using realizedIn_def by blast
    def forest == "(finsert \<gg> fempty)"
    from b1 forest_def have "forest \<in> (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>) state)"          by (simp add: \<open>\<And>\<gg>. (\<gg> \<in> \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>) state) = ((\<forall>tree.(tree|\<in>|\<gg> \<longrightarrow> evaluation (\<A> \<ii>) tree = state)) \<and> (\<exists> tree. tree |\<in>| \<gg>))\<close> language_for_state_def)
    from b1 forest_def have "(fset (pathsInForest  forest) \<subseteq> pathset)"              by (metis (full_types) fsingleton_iff notin_fset pathsTreeForest subset_iff)
    show "realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>) state) pathset"  using \<open>forest \<in> \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>) state\<close> \<open>fset (\<Pi>\<^sub>\<iota>\<^sub>\<phi> forest) \<subseteq> pathset\<close> \<open>realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>) state) pathset = (\<exists>\<gg>. \<gg> \<in> \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>) state \<and> fset (\<Pi>\<^sub>\<iota>\<^sub>\<phi> \<gg>) \<subseteq> pathset)\<close> by auto 
  }        
  {
    assume "realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>) state) pathset"
    then obtain forest where m1 : "forest \<in> (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>) state)" and m2 : "(fset (pathsInForest  forest) \<subseteq> pathset)"        using \<open>realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>) state) pathset = (\<exists>\<gg>. \<gg> \<in> \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>) state \<and> fset (\<Pi>\<^sub>\<iota>\<^sub>\<phi> \<gg>) \<subseteq> pathset)\<close> by blast 
    then obtain tr where m3 : "tr |\<in>| forest"      using \<open>\<And>\<gg>. (\<gg> \<in> \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>) state) = ((\<forall>tree. tree |\<in>| \<gg> \<longrightarrow> evaluation (\<A> \<ii>) tree = state) \<and> (\<exists>tree. tree |\<in>| \<gg>))\<close> by auto 
    then have  "tr \<in> (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> \<ii>) state)"      using \<open>\<And>\<gg>. (\<gg> \<in> \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>) state) = ((\<forall>tree. tree |\<in>| \<gg> \<longrightarrow> evaluation (\<A> \<ii>) tree = state) \<and> (\<exists>tree. tree |\<in>| \<gg>))\<close> language_for_state_def m1 by fastforce 
    have "fset (\<Pi> tr) \<subseteq> pathset" using m1 m2 m3  by (meson notin_fset pathsTreeForest subset_iff)
    show "realizedIn (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> \<ii>) state) pathset"      using \<open>fset (\<delta>\<^sub>\<tau> tr) \<subseteq> pathset\<close> \<open>realizedIn (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> \<ii>) state) pathset = (\<exists>\<gg>. \<gg> \<in> \<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> \<ii>) state \<and> fset (\<delta>\<^sub>\<tau> \<gg>) \<subseteq> pathset)\<close> \<open>tr \<in> \<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> \<ii>) state\<close> by auto 
  }
qed
  
  
  
definition necess :: "('Q,abc) tree_automaton \<Rightarrow> abc list set set \<Rightarrow> ('Q,abc) rule \<Rightarrow> abc list set set" where
  "necess automaton I r 
     = (\<lambda>x.(symbol r) \<bullet> x) ` {i . (i \<in> I) \<and> 
            (\<L>\<^sub>\<tau>\<^sub>\<rho> automaton r) \<subseteq> (existential_satisfaction_set ((symbol r) \<bullet> i))}"    
  
definition upwardClosure :: "('L list fset set \<Rightarrow> 'L list fset set)" where            
  "upwardClosure L = {tr . \<exists> t2 \<in> L . fset tr \<supseteq> fset t2}"
  
  
    (* ================================================================================ *)
    
    (* Here I'm showing a few basic facts about the maximum of a finite set of integers *)
    
lemma maxIsUnique :
  fixes x s
  assumes "((\<forall> y. (y|\<in>|s \<longrightarrow> y \<le> x)) \<and> (s = {||} \<longrightarrow> x=0) \<and> (s \<noteq> {||} \<longrightarrow> (x |\<in>| s)))"
  shows "x = maxFset s"
  by (metis antisym_conv assms finiteMaxExists(1) finiteMaxExists(2) finiteMaxExists(3))
    
    
    (* Addition commutes with Maximum *)
lemma maxAndSuc :
  shows  "\<And> (q :: nat fset) . q \<noteq> {||} \<Longrightarrow> maxFset (fimage (Suc) q) = 1 + maxFset q" 
proof -
  fix q :: "nat fset"
  assume "q \<noteq> {||}"
  then have "(fimage (Suc) q) \<noteq> {||}" by auto
  then have "((\<forall> y. (y|\<in>|(fimage (Suc) q) \<longrightarrow> y \<le> (1 + maxFset (fimage (Suc) q)))) \<and> ((fimage (Suc) q) = {||} \<longrightarrow> (1 + maxFset (fimage (Suc) q))=0) \<and> ((fimage (Suc) q) \<noteq> {||} \<longrightarrow> ((1 + maxFset q) |\<in>| (fimage (Suc) q))))"
    by (metis One_nat_def \<open>q \<noteq> {||}\<close> add.left_neutral add_Suc fimage_eqI finiteMaxExists(1) finiteMaxExists(3) trans_le_add2)
  then show "maxFset (fimage (Suc) q) = 1 + maxFset q" using  maxIsUnique
  proof -
    obtain nn :: "nat fset \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
      f1: "\<forall>x0 x1 x2. (\<exists>v3. x2 = x1 v3 \<and> v3 |\<in>| x0) = (x2 = x1 (nn x0 x1 x2) \<and> nn x0 x1 x2 |\<in>| x0)"
      by moura
    have "Suc |`| q \<noteq> {||}"
      using \<open>(\<forall>y. y |\<in>| Suc |`| q \<longrightarrow> y \<le> 1 + maxFset (Suc |`| q)) \<and> (Suc |`| q = {||} \<longrightarrow> 1 + maxFset (Suc |`| q) = 0) \<and> (Suc |`| q \<noteq> {||} \<longrightarrow> 1 + maxFset q |\<in>| Suc |`| q)\<close> by fastforce
    then have f2: "maxFset (Suc |`| q) = Suc (nn q Suc (maxFset (Suc |`| q))) \<and> nn q Suc (maxFset (Suc |`| q)) |\<in>| q"
      using f1 by (meson fimageE finiteMaxExists(3))
    then have f3: "nn q Suc (maxFset (Suc |`| q)) \<le> maxFset q"
      by (metis finiteMaxExists(1))
    have "0 + Suc (maxFset q) \<le> maxFset (Suc |`| q)"
      using \<open>(\<forall>y. y |\<in>| Suc |`| q \<longrightarrow> y \<le> 1 + maxFset (Suc |`| q)) \<and> (Suc |`| q = {||} \<longrightarrow> 1 + maxFset (Suc |`| q) = 0) \<and> (Suc |`| q \<noteq> {||} \<longrightarrow> 1 + maxFset q |\<in>| Suc |`| q)\<close> finiteMaxExists(1) by auto
    then show ?thesis
      using f3 f2 by linarith
  qed 
qed
  
  
  (* The maximum of a (finite) union of (finite) sets is equal to the maximum of the set of maxima of the sets *)
lemma maxDistrib :
  fixes f x2a g
  shows "maxFset ((g |`| ( (((\<Union>| (fimage f x2a))))))) = maxFset ((\<lambda> x. (maxFset  (g |`| (f x)))     ) |`| x2a)"
proof (rule disjE)
  def num == "maxFset ((\<lambda> x. (maxFset  (g |`| (f x)))     ) |`| x2a)"
  from num_def  have "\<And> x . x |\<in>| x2a \<Longrightarrow> (num \<ge> (maxFset  (g |`| (f x))))"    by (simp add: finiteMaxExists(1)) 
  hence "\<And> x y . x |\<in>| x2a \<Longrightarrow> y |\<in>| (g |`| (f x)) \<Longrightarrow> num \<ge> y"   by (meson finiteMaxExists(1) order_trans) 
  hence n400 : "\<And> y . y |\<in>| ((g |`| ( (((\<Union>| (fimage f x2a))))))) \<Longrightarrow> num \<ge> y" by auto
  def leftSet == "((g |`| ( (((\<Union>| (fimage f x2a)))))))"
  show "leftSet = {||}  \<or> leftSet \<noteq> {||}" by auto
  show "leftSet = {||} \<Longrightarrow> maxFset ((g |`| ( (((\<Union>| (fimage f x2a))))))) = maxFset ((\<lambda> x. (maxFset  (g |`| (f x)))     ) |`| x2a)"
  proof -
    assume m800 : "leftSet = {||}"
    hence m801 :  "maxFset ((g |`| ( (((\<Union>| (fimage f x2a))))))) = 0" using leftSet_def        by (simp add: finiteMaxExists(2))
    have m802 : "maxFset ((\<lambda> x. (maxFset  (g |`| (f x)))     ) |`| x2a) = 0"
    proof -
      from m800 leftSet_def have "( (((\<Union>| (fimage f x2a))))) = {||}"        by (simp add: leftSet_def)
      hence "\<And>x . (x |\<in>| x2a \<Longrightarrow> ( f x = {||}))"            by blast 
      hence "\<And>x . (x |\<in>| x2a \<Longrightarrow> ( maxFset (g |`| (f x)) = 0))"            by (simp add: finiteMaxExists(2))
      then show "maxFset ((\<lambda> x. (maxFset  (g |`| (f x)))     ) |`| x2a) = 0"            by (metis (no_types, lifting) fimageE finiteMaxExists(2) finiteMaxExists(3))
    qed
    from m801 m802 show "maxFset ((g |`| ( (((\<Union>| (fimage f x2a))))))) = maxFset ((\<lambda> x. (maxFset  (g |`| (f x)))     ) |`| x2a)" by auto
  qed
  show "leftSet \<noteq> {||} \<Longrightarrow> maxFset ((g |`| ( (((\<Union>| (fimage f x2a))))))) = maxFset ((\<lambda> x. (maxFset  (g |`| (f x)))     ) |`| x2a)" 
  proof -
    assume m900 : "leftSet \<noteq> {||}"
    then obtain member where m300 : "member |\<in>| leftSet" by auto
    from n400 leftSet_def have n500 :  "((\<forall> y. (y|\<in>|leftSet \<longrightarrow> y \<le> num)))"  by auto
    have n501 : "((num |\<in>| leftSet))"
    proof -
      from m900 leftSet_def have "(\<Union>| (fimage f x2a))  \<noteq> {||}" by simp
      then obtain member2 where "member2 |\<in>| x2a" and "f member2 \<noteq> {||}"            by fastforce
      then have "((\<lambda> x. (maxFset  (g |`| (f x)))     ) |`| x2a) \<noteq> {||}"            by auto
      then have "num |\<in>| ((\<lambda> x. (maxFset  (g |`| (f x)))     ) |`| x2a)" using num_def finiteMaxExists(3) by blast
      then obtain member3 where "member3 |\<in>| x2a" and y749 :  "num = (((maxFset  (g |`| (f member3)))     ))"            by blast
      show "num |\<in>| leftSet"
      proof (rule disjE)
        show "num = 0 \<or> num > 0" by auto
        show "num = 0 \<Longrightarrow> num |\<in>| leftSet"
        proof -
          from n500 have "num = 0 \<Longrightarrow> (\<And>y. y |\<in>| leftSet \<Longrightarrow> y = 0)" by simp
          then show "num = 0 \<Longrightarrow> num |\<in>| leftSet" using m300 by metis
        qed
        show "0 < num \<Longrightarrow> num |\<in>| leftSet"
        proof -
          assume y750 : "0 < num"
          then have "num |\<in>| g |`| (f member3)" using y749 finiteMaxExists            by (metis neq0_conv) 
          then show "num |\<in>| leftSet"            using \<open>member3 |\<in>| x2a\<close> leftSet_def by blast
        qed
      qed
    qed
    from n500 n501 have "((\<forall> y. (y|\<in>|leftSet \<longrightarrow> y \<le> num)) \<and> (leftSet = {||} \<longrightarrow> num=0) \<and> (leftSet \<noteq> {||} \<longrightarrow> (num |\<in>| leftSet)))" using m900 by auto
    show "leftSet \<noteq> {||} \<Longrightarrow> maxFset (g |`| \<Union>| (f |`| x2a)) = maxFset ((\<lambda>x. maxFset (g |`| f x)) |`| x2a)"      using leftSet_def maxIsUnique n500 n501 num_def by auto
  qed
qed
  
  
  
lemma maxFsetUnion :
  fixes a b
  shows  "maxFset (a |\<union>| b) = (max (maxFset a) (maxFset b))"
proof -
  have "max (maxFset a) (maxFset b) = maxFset {|maxFset a, maxFset b|}"    by (smt antisym_conv2 finiteMaxExists(1) finiteMaxExists(3) finsertI1 finsert_absorb finsert_iff finsert_not_fempty max_def not_le)
  then have "maxFset (a |\<union>| b) = maxFset {|maxFset a, maxFset b|}" using maxDistrib
    by (smt antisym_conv finiteMaxExists(1) finiteMaxExists(2) finiteMaxExists(3) fset_rev_mp funionE max_0R max_def sup_ge1 sup_ge2 sup_max)
  then show "maxFset (a |\<union>| b) = (max (maxFset a) (maxFset b))"    by (simp add: \<open>max (maxFset a) (maxFset b) = maxFset {|maxFset a, maxFset b|}\<close>)
qed
  
      
lemma maxMonotonic :
  assumes "( t |\<subseteq>|  s)"
  shows "maxFset t \<le> maxFset s"
  by (metis assms finiteMaxExists(1) finiteMaxExists(2) finiteMaxExists(3) fset_rev_mp le_0_eq nat_le_linear)
    
    
    (* ================================================================================ *)
  
  (* The height of a tree is equal to the maximal length of any of its paths *)
lemma heightOnlyDependsOnPaths :
  shows "height t = (maxFset (length |`| (\<Pi> t)))"
proof (induct t)
  case (NODE x1a x2a)
  assume q1 : "\<And>x2aa. x2aa \<in> fset x2a \<Longrightarrow> height x2aa = maxFset (length |`| \<delta>\<^sub>\<tau> x2aa)"
  have "height (NODE x1a x2a) = 1 + (maxFset (fimage height x2a))" by auto
  have n1 : "\<Pi> (NODE x1a x2a) = fimage (append [x1a]) ((\<Union>| (fimage \<Pi> x2a))  |\<union>|  (finsert [] {||}))" by auto
  have y10 : " (length |`| (fimage (append [x1a]) (\<Union>| (fimage \<Pi> x2a)))) =  (fimage (Suc) (length |`| ( (\<Union>| (fimage \<Pi> x2a)))))"        by (smt One_nat_def Suc_eq_plus1_left fimage_fimage fset.map_cong0 length_Cons length_append list.size(3)) 
  then have y1 : "maxFset (length |`| (fimage (append [x1a]) (\<Union>| (fimage \<Pi> x2a)))) = maxFset (fimage (Suc) (length |`| ( (\<Union>| (fimage \<Pi> x2a)))))" by auto
  have   "(((\<Union>| (fimage \<Pi> x2a))) |\<union>|  (finsert [] {||})) \<noteq> {||}"    using n1 by auto
  then have "(length |`| (((\<Union>| (fimage \<Pi> x2a))) |\<union>|  (finsert [] {||}))) \<noteq> {||}" by blast
  then have y2 : "maxFset (fimage (Suc) (length |`| ( (((\<Union>| (fimage \<Pi> x2a))) |\<union>|  (finsert [] {||}))))) = 1 + maxFset ((length |`| ( (((\<Union>| (fimage \<Pi> x2a))) |\<union>|  (finsert [] {||})))))" using maxAndSuc    by meson
  have y9 : "(maxFset (fimage height x2a)) = maxFset ((length |`| ( (((\<Union>| (fimage \<Pi> x2a))) |\<union>|  (finsert [] {||})))))"
  proof (rule disjE)
    show "x2a = {||} \<or> x2a \<noteq> {||}" by auto
    {
      assume o1 : "x2a = {||}"
      have "(maxFset (fimage height {||})) = maxFset {||}"  by auto
      then have s1 : "(maxFset (fimage height x2a)) = 0" using finiteMaxExists               by (simp add: o1)
      from o1 have " ( (((\<Union>| (fimage \<Pi> x2a))) |\<union>|  (finsert [] {||}))) = (finsert [] {||})"               by (simp add: ffUnion_empty) 
      then have s2 : "((length |`| ( (((\<Union>| (fimage \<Pi> x2a))) |\<union>|  (finsert [] {||}))))) = (finsert 0 {||})"               by auto  
      have s3 : "maxFset (finsert 0 {||}) = 0"               using finiteMaxExists(3) by blast
      from s3 have "maxFset ((length |`| ( (((\<Union>| (fimage \<Pi> x2a))) |\<union>|  (finsert [] {||}))))) = 0"               using s2 by presburger
      then show "(maxFset (fimage height x2a)) = maxFset ((length |`| ( (((\<Union>| (fimage \<Pi> x2a))) |\<union>|  (finsert [] {||})))))" using s1 by auto
    }
    {
      assume o1 : "x2a \<noteq> {||}"
      have "((length |`| ( (((\<Union>| (fimage \<Pi> x2a))) |\<union>|  (finsert [] {||}))))) = (length |`| ( (((\<Union>| (fimage \<Pi> x2a)))))) |\<union>| (length |`| (finsert [] {||}))"             by simp 
      from maxFsetUnion have r1 :  "maxFset ((length |`| ( (((\<Union>| (fimage \<Pi> x2a)))))) |\<union>| (length |`| (finsert [] {||}))) = max (maxFset ((length |`| ( (((\<Union>| (fimage \<Pi> x2a)))))))) (maxFset (length |`| (finsert [] {||})))"           by (metis \<open>length |`| (\<Union>| (\<delta>\<^sub>\<tau> |`| x2a) |\<union>| {|[]|}) = length |`| \<Union>| (\<delta>\<^sub>\<tau> |`| x2a) |\<union>| length |`| {|[]|}\<close>) 
      have r2 : "(maxFset (length |`| (finsert [] {||}))) = 0"               using finiteMaxExists(3) by auto
      then have r3 : "max (maxFset ((length |`| ( (((\<Union>| (fimage \<Pi> x2a)))))))) (maxFset (length |`| (finsert [] {||}))) = maxFset ((length |`| ( (((\<Union>| (fimage \<Pi> x2a)))))))"  by simp
      from r1 r2 r3   have k500 : "maxFset ((length |`| ( (((\<Union>| (fimage \<Pi> x2a)))))) |\<union>| (length |`| (finsert [] {||}))) = maxFset ((length |`| ( (((\<Union>| (fimage \<Pi> x2a)))))))"          by simp
      have "maxFset ((length |`| ( (((\<Union>| (fimage \<Pi> x2a))))))) = maxFset ((\<lambda> x. (maxFset  (length |`| (\<Pi> x)))     ) |`| x2a)"       by (simp add: maxDistrib) 
      then have k501 : "maxFset ((length |`| ( (((\<Union>| (fimage \<Pi> x2a))))))) = (maxFset (fimage height x2a))" using q1         using fset.map_cong0 by force 
      from k500 k501 show "maxFset (height |`| x2a) = maxFset (length |`| (\<Union>| (\<delta>\<^sub>\<tau> |`| x2a) |\<union>| {|[]|}))" by simp
    }
  qed
  have y3 : "1 + (maxFset (fimage height x2a)) = maxFset (length |`| (fimage (append [x1a]) (((\<Union>| (fimage \<Pi> x2a))) |\<union>|  (finsert [] {||}))))"    using y1 y2 y9    using y10 by auto 
  then have y4 : "1 + (maxFset (fimage height x2a)) = maxFset (length |`| \<delta>\<^sub>\<tau> (NODE x1a x2a))" using n1 by auto
  then show "height (NODE x1a x2a) = maxFset (length |`| \<delta>\<^sub>\<tau> (NODE x1a x2a))"    by simp
qed
  
  
  
lemma heightOfChild:
  assumes b1 : "x |\<in>| childrenSet tree"
  shows "height x < height tree"
proof -
  obtain symb2 set2 where b2:  "tree = (NODE symb2 set2)"    using tree.exhaust by blast
  from b2 have b5 : "height tree = 1 + (maxFset (fimage height set2))" using height.simps by auto
  from b1 b2 have "x |\<in>| set2" by (simp add: childrenSet.simps)
  then have "height x \<le> (maxFset (fimage height set2))"        by (simp add: finiteMaxExists)
  then show ?thesis using b5 by arith
qed
    
lemma childDepth :
  assumes "child |\<in>| children"
    shows "height (NODE parent children) > ((height child))"
  by (metis assms childrenSet.simps heightOfChild)
    
    
  (* --------------------------------------------------------- *)
  (*  PSI, the distributive normal form  *)
  (* --------------------------------------------------------- *)
    
function psi :: "abc tree \<Rightarrow> abc tree" where
  "psi (NODE symbol1 children1)
      = NODE symbol1 (fimage (\<lambda> symbol2 .
                              psi (NODE symbol2 (\<Union>| (fimage childrenSet (childrenWithSymbol symbol2 children1)))
                                  )
                              )
                              (fimage root children1)
                     )"
  by pat_completeness auto
(*termination apply (relation "measure height")
proof -
  show "wf (measure height)" by auto
  show "\<And>symbol1 children1 z. z \<in> fset (root |`| children1) \<Longrightarrow> (NODE z (\<Union>| (childrenSet |`| childrenWithSymbol z children1)), NODE symbol1 children1) \<in> measure height"
  proof (simp add : measure_def)
    fix children1 z
    def upMax == "maxFset (height |`| children1)"
    def downMax == "maxFset (height |`| \<Union>| (childrenSet |`| childrenWithSymbol z children1))"
    show "z \<in> root ` fset children1 \<Longrightarrow> maxFset (height |`| \<Union>| (childrenSet |`| childrenWithSymbol z children1)) < maxFset (height |`| children1)"
    proof -
      assume n875654 : "z \<in> root ` fset children1"
      have "downMax < upMax"
      proof (rule disjE)
        show "height |`| \<Union>| (childrenSet |`| childrenWithSymbol z children1) = fempty \<or> height |`| \<Union>| (childrenSet |`| childrenWithSymbol z children1) \<noteq> fempty" by auto
        {
          assume "height |`| \<Union>| (childrenSet |`| childrenWithSymbol z children1) = fempty"
          hence "downMax = 0" using downMax_def           using finiteMaxExists(2) by auto 
          from n875654 obtain tree where "z = root tree" and "tree |\<in>| children1" using childrenWithSymbol_def equalsffemptyD fimageE fimage_is_fempty imageE notin_fset    by fastforce  
          hence "height tree \<le> upMax" using upMax_def      by (simp add: finiteMaxExists(1)) 
          from theSingletonPathExists heightOnlyDependsOnPaths finiteMaxExists(3) have "height tree > 0"              by (metis fimage_eqI finiteMaxExists(1) gr0I impossible_Cons list.size(3) rootIsPath2) 
          then show "downMax < upMax"              using \<open>downMax = 0\<close> \<open>height tree \<le> upMax\<close> less_le_trans by blast 
        }
        {
          assume "height |`| \<Union>| (childrenSet |`| childrenWithSymbol z children1) \<noteq> fempty"
          then obtain child tree where "tree |\<in>| childrenWithSymbol z children1" and n764543 : "child |\<in>| childrenSet tree" and nu754543 : "height child = downMax" using ffUnionLemma    downMax_def  finiteMaxExists(3)              by (smt fimageE) 
          hence ni8764543 : "tree |\<in>| children1" using childrenWithSymbol_def                  by (metis finterD1) 
          have  "downMax < height tree" using n764543 nu754543        using heightOfChild by blast 
          then show "downMax < upMax" using upMax_def ni8764543 finiteMaxExists(1)            by (metis fimage_eqI less_le_trans) 
        }
      qed
      then show "z \<in> root ` fset children1 \<Longrightarrow> maxFset (height |`| \<Union>| (childrenSet |`| childrenWithSymbol z children1)) < maxFset (height |`| children1)" using upMax_def downMax_def by auto
    qed
  qed
qed*)
  

definition psiF where "psiF trees = fimage (\<lambda> symbol2 .
                              psi (NODE symbol2 (\<Union>| (fimage childrenSet (childrenWithSymbol symbol2 trees)))
                                  )
                              )
                              (fimage root trees)"
  
  
  
abbreviation psiFAbb :: "abc tree fset \<Rightarrow> abc tree fset" ("\<Psi>\<^sub>\<phi>") where "\<Psi>\<^sub>\<phi> x \<equiv> psiF x"
  
definition psiFLang where "psiFLang language = \<Psi>\<^sub>\<phi> ` language"
  
    
definition \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> :: "stt fset \<Rightarrow> stt fset \<Rightarrow> abc tree fset set" where
  "\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2 = ( ((\<Psi>\<^sub>\<phi> `(\<Uplus> ( ((\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1) |`| Sa1)))) 
                                    \<inter> (\<Psi>\<^sub>\<phi> `(\<Uplus> ( ((\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2) |`| Sa2))))))"
definition \<Psi>\<^sub>\<Sigma>\<^sub>\<rho> :: "(stt,abc) rule fset \<Rightarrow> (stt,abc) rule fset \<Rightarrow> abc tree fset set" where
  "\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> Sa1 Sa2 = ( ((\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| Sa1)))) 
                                              \<inter> (\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>2) |`| Sa2))))))" 
  
  
  
definition \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> :: "stt fset \<Rightarrow> stt fset \<Rightarrow> abc list fset set" where
  "\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2 = ( (((\<Uplus>\<^sub>\<delta> ( ((\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1) |`| Sa1)))) 
                                    \<inter> ((\<Uplus>\<^sub>\<delta> ( ((\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2) |`| Sa2))))))"
definition \<Psi>\<^sub>\<Sigma>\<^sub>\<rho>\<^sub>\<delta> :: "(stt,abc) rule fset \<Rightarrow> (stt,abc) rule fset \<Rightarrow> abc list fset set" where
  "\<Psi>\<^sub>\<Sigma>\<^sub>\<rho>\<^sub>\<delta> Sa1 Sa2 = ( (((\<Uplus>\<^sub>\<delta> (((\<delta>\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| Sa1)))) 
                                              \<inter> ((\<Uplus>\<^sub>\<delta> (((\<delta>\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>2) |`| Sa2))))))" 
  
  
  
  
  
definition dist_intersectionLanguageOplusD :: "stt fset \<Rightarrow> stt fset \<Rightarrow> abc list fset set" where
  "dist_intersectionLanguageOplusD Sa1 Sa2 = ( (((\<Oplus>\<^sub>\<delta> ( (\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1) |`| Sa1))) 
                       \<inter> ( (\<Oplus>\<^sub>\<delta> ((\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2) |`| Sa2)))))"
definition dist_intersectionLanguageOplusRulesD :: "(stt,abc) rule fset \<Rightarrow> (stt,abc) rule fset \<Rightarrow> abc list fset set" where
  "dist_intersectionLanguageOplusRulesD Sa1 Sa2 = ( (((\<Oplus>\<^sub>\<delta> ( (\<delta>\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| Sa1))) 
                            \<inter> ((\<Oplus>\<^sub>\<delta> ((\<delta>\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>2) |`| Sa2)))))"                                                  
  
definition dist_intersectionLanguageOplus :: "stt fset \<Rightarrow> stt fset \<Rightarrow> abc tree fset set" where
  "dist_intersectionLanguageOplus Sa1 Sa2 = ( ((\<Psi>\<^sub>\<phi> `(\<Oplus> ( (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1) |`| Sa1))) 
                       \<inter> ( \<Psi>\<^sub>\<phi> `(\<Oplus> ((\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2) |`| Sa2)))))"
definition dist_intersectionLanguageOplusRules :: "(stt,abc) rule fset \<Rightarrow> (stt,abc) rule fset \<Rightarrow> abc tree fset set" where
  "dist_intersectionLanguageOplusRules Sa1 Sa2 = ( ((\<Psi>\<^sub>\<phi> `(\<Oplus> ( (\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| Sa1))) 
                            \<inter> (\<Psi>\<^sub>\<phi> ` (\<Oplus> ((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>2) |`| Sa2)))))"                                               
  
  
abbreviation dist_intersectionLanguageOplusAbb :: "stt fset \<Rightarrow> stt fset \<Rightarrow> abc tree fset set" ("\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma>") where "\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma> x y \<equiv> dist_intersectionLanguageOplus x y"
abbreviation dist_intersectionLanguageOplusRulesAbb :: "(stt,abc) rule fset \<Rightarrow> (stt,abc) rule fset \<Rightarrow> abc tree fset set" ("\<Psi>\<^sub>\<Oplus>\<^sub>\<rho>") where "\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> x y \<equiv> dist_intersectionLanguageOplusRules x y"
  
abbreviation dist_intersectionLanguageOplusAbbD :: "stt fset \<Rightarrow> stt fset \<Rightarrow> abc list fset set" ("\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma>\<^sub>\<delta>") where "\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma>\<^sub>\<delta> x y \<equiv> dist_intersectionLanguageOplusD x y"
abbreviation dist_intersectionLanguageOplusRulesAbbD :: "(stt,abc) rule fset \<Rightarrow> (stt,abc) rule fset \<Rightarrow> abc list fset set" ("\<Psi>\<^sub>\<Oplus>\<^sub>\<rho>\<^sub>\<delta>") where "\<Psi>\<^sub>\<Oplus>\<^sub>\<rho>\<^sub>\<delta> x y \<equiv> dist_intersectionLanguageOplusRulesD x y"
  
  
  

    
    
    
    
    
    (* ============================================= *)
section "Basic Lemma On Approximation Beyond N"
  
  
  
  
definition \<I> :: "abc list set set" where
  "\<I> = (\<lambda>pair . \<pi>\<^sup>1 pair - \<pi>\<^sup>2 pair) `
                     {setPair . (\<exists> i Sa1 Sa2 s . 
(*                                (((s |\<in>| (state_set) (\<A> i))) \<and> (((Sa1 |\<subseteq>| (state_set) \<A>\<^sub>1))) \<and> ((Sa2 |\<subseteq>| (state_set) \<A>\<^sub>2)) \<and>*)
                                (\<pi>\<^sup>1 setPair = (\<Pi>\<^sub>\<phi> (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) s))) 
                              \<and> (\<pi>\<^sup>2 setPair = (\<Pi>\<^sub>\<delta> (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta>  Sa1 Sa2))))}"
  
  
definition constantIsSuitableForStates :: "ot \<Rightarrow> stt \<Rightarrow> stt fset \<Rightarrow> stt fset \<Rightarrow> nat \<Rightarrow> bool" where
  "constantIsSuitableForStates i s Sa1 Sa2 N = (\<exists> I \<in> \<I>. ((\<forall> n . ((Suc n > N) \<longrightarrow> ((\<not>(realizedIn 
                                                           (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) s)  
                                                           (\<Pi>\<^sub>\<delta> (fset (\<Z>\<^sub>\<delta> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2) )))
                                                     ) )
                                                     \<longrightarrow> ( ( ( (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) s) \<Turnstile> I)
                                                                       \<and> ((I \<inter> \<Pi>\<^sub>\<delta> ( (( \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2  )))) = {})
                                                                      )
                                                               )
                                                          )
                                            ))))"
  
definition constantIsSuitableForAllStates  :: "nat \<Rightarrow> bool" where
  "constantIsSuitableForAllStates N = (\<forall> i . 
                                         (\<forall> s . 
                                           (\<forall> Sa1 . 
                                             (\<forall> Sa2 . (s |\<in>| (state_set (\<A> i))
                                                        \<longrightarrow>  ( Sa1 |\<subseteq>| state_set \<A>\<^sub>1 
                                                           \<longrightarrow> ( Sa2 |\<subseteq>| state_set \<A>\<^sub>2 
                                                               \<longrightarrow> ( constantIsSuitableForStates i s Sa1 Sa2 N
               ))))))))"
  
definition heightForestBounded :: "abc tree fset \<Rightarrow> nat \<Rightarrow> bool" where
  "heightForestBounded \<ff> n = (\<forall>t.(t|\<in>|\<ff> \<longrightarrow> height t \<le> n))"
  
    
  
lemma factorByRootSymbolF_lemma :
  fixes symb
  fixes language
  shows "\<And>a. ((a |\<in>| symb \<diamondop> language) = (a \<in> factorByRootSymbol symb (fset language)))"
    and "fset  ( symb \<diamondop> language) = factorByRootSymbol symb (fset language)"
proof -
  have k9 : "finite {t. (\<exists>tree . tree |\<in>| language \<and> (root tree = symb \<and> t |\<in>| childrenSet tree))}"
  proof -
    def setsOfChildren == "\<Union>| (childrenSet |`| (ffilter (\<lambda> tr . root tr = symb) language))"
    have "\<And>x . ((x |\<in>| (\<Union>| (childrenSet |`| (ffilter (\<lambda> tr . root tr = symb) language)))) = (x \<in> {t. (\<exists>tree . tree |\<in>| language \<and> (root tree = symb \<and> t |\<in>| childrenSet tree))}))"
    proof -
      fix x
      from setsOfChildren_def have "((x |\<in>| (\<Union>| (childrenSet |`| (ffilter (\<lambda> tr . root tr = symb) language))))  = (\<exists> y. ( y|\<in>| (ffilter (\<lambda> tr . root tr = symb) language) \<and> x |\<in>| childrenSet y    )))"        by auto
      also have "... = (\<exists> y. ( y|\<in>| language \<and> root y = symb \<and> x |\<in>| childrenSet y    ))" by auto
      also have "... = (x \<in> {t. (\<exists>tree . tree |\<in>| language \<and> (root tree = symb \<and> t |\<in>| childrenSet tree))})" by auto
      then show "((x |\<in>| (\<Union>| (childrenSet |`| (ffilter (\<lambda> tr . root tr = symb) language)))) = (x \<in> {t. (\<exists>tree . tree |\<in>| language \<and> (root tree = symb \<and> t |\<in>| childrenSet tree))}))" by auto
    qed
    then   have "\<And>x . ((x |\<in>| setsOfChildren) = (x \<in> {t. (\<exists>tree . tree |\<in>| language \<and> (root tree = symb \<and> t |\<in>| childrenSet tree))}))" using setsOfChildren_def by auto 
    then  have "(fset setsOfChildren) = {t. (\<exists>tree . tree |\<in>| language \<and> (root tree = symb \<and> t |\<in>| childrenSet tree))}"        by (meson notin_fset subsetI subset_antisym)  
    then show "finite {t. (\<exists>tree . tree |\<in>| language \<and> (root tree = symb \<and> t |\<in>| childrenSet tree))}"            by (metis finite_fset)
  qed
    
  show "\<And>a. ((a |\<in>| symb \<diamondop> language) = (a \<in> factorByRootSymbol symb (fset language)))"
  proof -
    fix a
    show "(a |\<in>| symb \<diamondop> language) = (a \<in> symb \<diamondop>\<tau>\<lambda> fset language)"
    proof -
      from factorByRootSymbolF_def have i1a : "(a |\<in>| symb \<diamondop> language) = (a |\<in>| set_to_fset {t. (\<exists>tree . tree |\<in>| language \<and> (root tree = symb \<and> t |\<in>| childrenSet tree))})" by auto
      from factorByRootSymbol_def have "(a \<in> symb \<diamondop>\<tau>\<lambda> fset language) = (a \<in> {t. (\<exists>tree \<in> fset language . (root tree = symb \<and> t |\<in>| childrenSet tree))})" by auto
      also have "... = (a \<in> {t. (\<exists>tree . tree |\<in>| language \<and> (root tree = symb \<and> t |\<in>| childrenSet tree))})"          by (smt mem_Collect_eq notin_fset) 
      from k9 set_to_fset_def have "(a |\<in>| set_to_fset {t. (\<exists>tree . tree |\<in>| language \<and> (root tree = symb \<and> t |\<in>| childrenSet tree))}) = (a \<in> {t. (\<exists>tree . tree |\<in>| language \<and> (root tree = symb \<and> t |\<in>| childrenSet tree))})"      by (metis (mono_tags, lifting) Abs_fset_inverse mem_Collect_eq notin_fset) 
      then show "(a |\<in>| symb \<diamondop> language) = (a \<in> symb \<diamondop>\<tau>\<lambda> fset language)" using calculation i1a          using \<open>(a \<in> {t. \<exists>tree\<in>fset language. root tree = symb \<and> t |\<in>| childrenSet tree}) = (a \<in> {t. \<exists>tree. tree |\<in>| language \<and> root tree = symb \<and> t |\<in>| childrenSet tree})\<close> by blast
    qed
  qed
    
  show "fset (symb \<diamondop> language) = symb \<diamondop>\<tau>\<lambda> fset language"    by (meson \<open>\<And>a. (a |\<in>| symb \<diamondop> language) = (a \<in> symb \<diamondop>\<tau>\<lambda> fset language)\<close> notin_fset subsetI subset_antisym) 
qed
  
definition heightD where "heightD pathset = (maxFset (length |`| pathset))"
  
lemma heightHeightD :
  shows "height tr = heightD (\<Pi> tr)"
  using  heightOnlyDependsOnPaths heightD_def  by (simp add: heightD_def) 
    
    
  
    
lemma unionAppend :
  shows "\<And>q . (\<alpha> \<bullet> q) \<union> {[\<alpha>]} = \<alpha> \<bullet> (q \<union> {[]})"
proof 
  fix q
  show "(\<alpha> \<bullet> q) \<union> {[\<alpha>]} \<subseteq> \<alpha> \<bullet> (q \<union> {[]})"
  proof 
    fix x
    assume "x \<in> \<alpha> \<bullet> q \<union> {[\<alpha>]}"
    hence "x \<in> \<alpha> \<bullet> q \<or> x \<in> {[\<alpha>]}"  by auto
    then show "x \<in> \<alpha> \<bullet> (q \<union> {[]})"  using prefixLetter_def  by auto
  qed
  show "\<alpha> \<bullet> (q \<union> {[]}) \<subseteq> \<alpha> \<bullet> q \<union> {[\<alpha>]}"
  proof
    fix x
    assume " x \<in> \<alpha> \<bullet> (q \<union> {[]})"
    then have "x \<in> \<alpha> \<bullet> q \<or> x \<in> \<alpha> \<bullet> {[]}" using prefixLetter_def  by auto
    then have "x \<in> \<alpha> \<bullet> q \<or> x \<in> {[\<alpha>]}" using prefixLetter_def  by auto
    then show " x \<in> (\<alpha> \<bullet> q) \<union> {[\<alpha>]}" by auto
  qed
qed
  
  
lemma realized_rule_state : 
  fixes \<alpha> :: "abc"
  assumes "symbol r = \<alpha>"
  assumes "realizedIn (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) r) (\<alpha> \<bullet> (pathset \<union> {[]}))"
  assumes "state |\<in>| (states r)"
  shows "(realizedIn  (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> \<ii>) state) pathset)"
proof -
  from assms realizedIn_def obtain \<gg> where a1 : " ((\<gg> \<in> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) r)))" and a2 :"(fset (\<Pi> \<gg>) \<subseteq> (\<alpha> \<bullet> (pathset \<union> {[]})))" by metis
  from a1 tree_for_rule_def language_for_rule_def have a10 : "((root \<gg> = symbol r) \<and> ((fimage (((evaluation (\<A> \<ii>)))) (childrenSet \<gg>)) = states r))" by blast
  then obtain child where a12 : "child |\<in>| childrenSet \<gg>" and "((evaluation (\<A> \<ii>))) child = state" using assms(3)        by (metis fimageE)  
  then have a30 : "child \<in> (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> \<ii>) state)" using language_for_state_def    by (simp add: language_for_state_def) 
  from a10 assms(1)  have a11 : "((root \<gg> = \<alpha>))" by auto 
  from pathAlternateDef  root.simps a11 have a25 : "\<Pi> \<gg> = op # \<alpha> |`| ((\<Union>| (\<Pi> |`| (childrenSet \<gg>))) |\<union>| {|[]|})"    by (metis childrenSet.elims) 
  have "((\<lambda> x.(\<alpha>#x)) ` (fset (\<Pi> child))) \<subseteq> (fset (\<Pi> \<gg>))"
  proof 
    fix x
    assume "x \<in> ((\<lambda> x.(\<alpha>#x)) ` (fset (\<Pi> child)))"
    then obtain y where a20 : "x = \<alpha>#y" and "y \<in> (fset (\<Pi> child))" by auto
    then have "y |\<in>| (\<Union>| (\<Pi> |`| (childrenSet \<gg>)))" using notin_fset a12          by (metis (full_types) ffUnionI fimage_eqI)
    then have "y |\<in>| (((\<Union>| (\<Pi> |`| (childrenSet \<gg>))) |\<union>| {|[]|}))" by auto
    then have "x |\<in>| op # \<alpha> |`| ((\<Union>| (\<Pi> |`| (childrenSet \<gg>))) |\<union>| {|[]|})" using a20 by auto
    then show "x \<in> (fset (\<Pi> \<gg>))" using a25 notin_fset by metis
  qed
  then have "(\<alpha> \<bullet> (fset (\<Pi> child))) \<subseteq> (fset (\<Pi> \<gg>))"      by (simp add: prefixLetter_def) 
  then have "(\<alpha> \<bullet> (fset (\<Pi> child))) \<subseteq> (\<alpha> \<bullet> (pathset \<union> {[]}))" using a2        by auto
  then have "((\<lambda> x.(\<alpha>#x)) ` (fset (\<Pi> child))) \<subseteq> ((\<lambda> x.(\<alpha>#x)) ` (pathset \<union> {[]}))" using a2   prefixLetter_def     by auto
  then have "(fset (\<Pi> child)) \<subseteq> ((pathset \<union> {[]}))"        by blast 
  then have "(fset (\<Pi> child)) \<subseteq> ((pathset))"
  proof -
    obtain aas :: "abc list set \<Rightarrow> abc list set \<Rightarrow> abc list" where
      f1: "\<forall>A Aa. (\<not> A \<subseteq> Aa \<or> (\<forall>as. as \<notin> A \<or> as \<in> Aa)) \<and> (aas A Aa \<in> A \<and> aas A Aa \<notin> Aa \<or> A \<subseteq> Aa)"
      by moura
    moreover
    { assume "[] \<noteq> aas (fset (\<delta>\<^sub>\<tau> child)) pathset"
      then have "aas (fset (\<delta>\<^sub>\<tau> child)) pathset \<in> fset (\<delta>\<^sub>\<tau> child) \<longrightarrow> fset (\<delta>\<^sub>\<tau> child) \<subseteq> pathset"
        using f1 by (metis Un_iff \<open>fset (\<delta>\<^sub>\<tau> child) \<subseteq> pathset \<union> {[]}\<close> all_not_in_conv insert_iff) }
    ultimately show ?thesis
      by (metis (no_types) list.distinct(1) noEmptyPathsInPi notin_fset)
  qed       
  then  have " ((child \<in> (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> \<ii>) state)))" and  "(fset (\<Pi> child) \<subseteq> ( (pathset)))" using a30 by auto
      then show "realizedIn (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> \<ii>) state) pathset"        using realizedIn_def by auto
qed
  
  
  
  
proposition commuteExistsAll :
  fixes D :: "'a fset"
  fixes P :: "'a \<Rightarrow> nat \<Rightarrow> bool"
  assumes  "\<And> d .  d |\<in>| D \<Longrightarrow> (\<exists> n. (\<forall> n2 . (n2 > n \<longrightarrow> P d n2)))"
  shows  "(\<exists> N. \<forall> d . d |\<in>| D \<longrightarrow> ((\<forall> n2 . (n2 > N \<longrightarrow> P  d n2))))"
proof -
  def choices == "\<lambda> d. (SOME n. ((\<forall> n2 . (n2 > n \<longrightarrow> P d n2))))"
  have ny756787 : "\<And> d .  d |\<in>| D \<Longrightarrow>(\<And> n2 . (n2 > (choices d) \<Longrightarrow> P d n2))" 
  proof -
    fix d
    assume "d |\<in>| D"
    hence "(\<exists> n. (\<forall> n2 . (n2 > n \<longrightarrow> P d n2)))" using assms by auto
    hence "(\<forall> n2 . (n2 > (choices d) \<longrightarrow> P d n2))" using choices_def          by (smt someI_ex) 
    then show "(\<And> n2 . (n2 > (choices d) \<Longrightarrow> P d n2))" by auto
  qed
  def maxChoice == "maxFset (choices |`| D)"
  hence "\<And> d .  d |\<in>| D \<Longrightarrow>(\<And> n2 . (n2 > maxChoice \<Longrightarrow> P d n2))" using ny756787      by (metis dual_order.strict_trans fimage_eqI finiteMaxExists(1) leD linorder_neqE_nat) 
  then show ?thesis by auto
qed
  
  
proposition commuteExistsAll2 :
  shows  "\<And> (P :: 'a \<Rightarrow> nat \<Rightarrow> bool) (D :: 'a fset) . ((\<forall> d .  d |\<in>| D \<longrightarrow> (\<exists> n. (\<forall> n2 . (n2 > n \<longrightarrow> P d n2)))) \<longrightarrow> (\<exists> N. \<forall> d . d |\<in>| D \<longrightarrow> ((\<forall> n2 . (n2 > N \<longrightarrow> P  d n2)))))"
  using commuteExistsAll by auto
    
      
      
proposition chainMaximum :
  fixes A :: "'a fset"
  fixes B :: "'b fset"
  fixes C :: "'c fset"
  fixes D :: "'d fset"
  fixes P :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> nat \<Rightarrow> bool"
  assumes "\<And> a b c d . a |\<in>| A \<Longrightarrow> b|\<in>|B \<Longrightarrow> c |\<in>| C \<Longrightarrow> d |\<in>| D \<Longrightarrow> (\<exists> n. (\<forall> n2 . (n2 > n \<longrightarrow> P a b c d n2)))"
  shows "\<exists> N. (\<forall> a b c d . a |\<in>| A \<longrightarrow> b|\<in>|B \<longrightarrow> c |\<in>| C \<longrightarrow> d |\<in>| D \<longrightarrow> ((\<forall> n2 . (n2 > N \<longrightarrow> P a b c d n2))))"
proof -
  from commuteExistsAll2 have n54687a : "\<And>(P :: 'a \<Rightarrow> nat \<Rightarrow> bool)  (D :: 'a fset). ((\<forall>d. d |\<in>| D \<longrightarrow> (\<exists>n. \<forall>n2>n. P d n2)) \<longrightarrow> (\<exists>N. \<forall>d. d |\<in>| D \<longrightarrow> (\<forall>n2>N. P d n2)))" by auto
  from commuteExistsAll2 have n54687b : "\<And>(P :: 'b \<Rightarrow> nat \<Rightarrow> bool)  (D :: 'b fset). ((\<forall>d. d |\<in>| D \<longrightarrow> (\<exists>n. \<forall>n2>n. P d n2)) \<longrightarrow> (\<exists>N. \<forall>d. d |\<in>| D \<longrightarrow> (\<forall>n2>N. P d n2)))" by auto
  from commuteExistsAll2 have n54687c : "\<And>(P :: 'c \<Rightarrow> nat \<Rightarrow> bool)  (D :: 'c fset). ((\<forall>d. d |\<in>| D \<longrightarrow> (\<exists>n. \<forall>n2>n. P d n2)) \<longrightarrow> (\<exists>N. \<forall>d. d |\<in>| D \<longrightarrow> (\<forall>n2>N. P d n2)))" by auto
  from commuteExistsAll2 have n54687d : "\<And>(P :: 'd \<Rightarrow> nat \<Rightarrow> bool)  (D :: 'd fset). ((\<forall>d. d |\<in>| D \<longrightarrow> (\<exists>n. \<forall>n2>n. P d n2)) \<longrightarrow> (\<exists>N. \<forall>d. d |\<in>| D \<longrightarrow> (\<forall>n2>N. P d n2)))" by auto
      
  have j1 : "(\<And> a b c  . a |\<in>| A \<Longrightarrow> b|\<in>|B \<Longrightarrow> c |\<in>| C \<Longrightarrow> (\<exists> N. \<forall> d . d |\<in>| D \<longrightarrow> ((\<forall> n2 . (n2 > N \<longrightarrow> P a b c d n2)))))"
  proof -
    fix a b c
    def Q == "P a b c"
    assume "a |\<in>| A" and  "b|\<in>|B" and "c |\<in>| C"
    then have n6578 : "\<forall> d . d |\<in>| D \<longrightarrow> (\<exists> n. (\<forall> n2 . (n2 > n \<longrightarrow> Q d n2)))" using Q_def assms        by auto
    from n6578 n54687d have " (\<exists> N. \<forall> d . d |\<in>| D \<longrightarrow> ((\<forall> n2 . (n2 > N \<longrightarrow> Q d n2))))" by auto
    then show "(\<exists> N. \<forall> d . d |\<in>| D \<longrightarrow> ((\<forall> n2 . (n2 > N \<longrightarrow> P a b c d n2))))" using Q_def by auto
  qed
    
  then have j2 : "(\<And> a b   . a |\<in>| A \<Longrightarrow> b|\<in>|B \<Longrightarrow> (\<exists> N. \<forall> c. c |\<in>| C \<longrightarrow> (\<forall> d . d |\<in>| D \<longrightarrow> ((\<forall> n2 . (n2 > N \<longrightarrow> P a b c d n2))))))" 
  proof -
    fix a b 
    assume "a |\<in>| A" and  "b|\<in>|B"
    then have "(\<And>  c  .  c |\<in>| C \<Longrightarrow> (\<exists> N. \<forall> d . d |\<in>| D \<longrightarrow> ((\<forall> n2 . (n2 > N \<longrightarrow> P a b c d n2)))))" using j1 by auto
    then have n6787 : "(\<And>  c  .  c |\<in>| C \<Longrightarrow> (\<exists> N. (\<forall> n2 . (n2 > N \<longrightarrow> (\<forall> d . d |\<in>| D \<longrightarrow> (P a b c d n2))))))" by blast
    def Q == "\<lambda> c n2. ((\<forall> d . d |\<in>| D \<longrightarrow> (P a b c d n2)))"
    then have "(\<And>  (c :: 'c)  .  c |\<in>| C \<Longrightarrow> (\<exists> N. (\<forall> n2 . (n2 > N \<longrightarrow> ((Q c n2))))))" using n6787 by blast 
    then have "(\<exists> N. \<forall>  c  .  c |\<in>| C \<longrightarrow> (\<forall> n2 . (n2 > N \<longrightarrow> ( ((Q c n2))))))" using n54687c  by auto
    then have "(\<exists> N. (\<forall> n2 . (n2 > N \<longrightarrow> (\<forall>  c  .  c |\<in>| C \<longrightarrow> ((Q c n2))))))" by blast
    then show "(\<exists> N. \<forall> c. c |\<in>| C \<longrightarrow> (\<forall> d . d |\<in>| D \<longrightarrow> ((\<forall> n2 . (n2 > N \<longrightarrow> P a b c d n2)))))" using Q_def by blast
  qed
    
  then have j3 : "(\<And> a   . a |\<in>| A \<Longrightarrow> (\<exists> N. (\<forall> b. b|\<in>|B \<longrightarrow>  (\<forall> c. c |\<in>| C \<longrightarrow> (\<forall> d . d |\<in>| D \<longrightarrow> ((\<forall> n2 . (n2 > N \<longrightarrow> P a b c d n2))))))))"
  proof -
    fix a 
    assume "a |\<in>| A"
    then have "(\<And>  b   .  b|\<in>|B \<Longrightarrow> (\<exists> N. \<forall> c. c |\<in>| C \<longrightarrow> (\<forall> d . d |\<in>| D \<longrightarrow> ((\<forall> n2 . (n2 > N \<longrightarrow> P a b c d n2))))))"  using j2 by auto
    then have n6787 : "(\<And>  b   .  b|\<in>|B \<Longrightarrow> (\<exists> N. (\<forall> n2 . (n2 > N \<longrightarrow> (\<forall> c. c |\<in>| C \<longrightarrow> (\<forall> d . d |\<in>| D \<longrightarrow> (P a b c d n2)))))))"  by blast
    def Q == "\<lambda> b n2. ((\<forall> c. c |\<in>| C \<longrightarrow> (\<forall> d . d |\<in>| D \<longrightarrow> (P a b c d n2))))"
    then have "(\<And>  b   .  b|\<in>|B \<Longrightarrow> (\<exists> N. (\<forall> n2 . (n2 > N \<longrightarrow> Q b n2))))" using n6787 by blast 
    then have "\<exists> N. (\<forall>    b   .  b|\<in>|B \<longrightarrow>((\<forall> n2 . (n2 > N \<longrightarrow> Q b n2))))" using n54687b  by auto
    then show "((\<exists> N. (\<forall> b. b|\<in>|B \<longrightarrow>  (\<forall> c. c |\<in>| C \<longrightarrow> (\<forall> d . d |\<in>| D \<longrightarrow> ((\<forall> n2 . (n2 > N \<longrightarrow> P a b c d n2))))))))" using Q_def by blast
  qed
  then have "(\<exists> N. (\<forall> a . (a |\<in>| A \<longrightarrow> (\<forall> b. b|\<in>|B \<longrightarrow>  (\<forall> c. c |\<in>| C \<longrightarrow> (\<forall> d . d |\<in>| D \<longrightarrow> ((\<forall> n2 . (n2 > N \<longrightarrow> P a b c d n2)))))))))"
  proof -
    have "(\<And> a   . a |\<in>| A \<Longrightarrow> (\<exists> N. (\<forall> b. b|\<in>|B \<longrightarrow>  (\<forall> c. c |\<in>| C \<longrightarrow> (\<forall> d . d |\<in>| D \<longrightarrow> ((\<forall> n2 . (n2 > N \<longrightarrow> P a b c d n2))))))))"  using j3 by auto
    hence "(\<And> a   . a |\<in>| A \<Longrightarrow> (\<exists> N.  (\<forall> b. b|\<in>|B \<longrightarrow>  (\<forall> c. c |\<in>| C \<longrightarrow> (\<forall> d .\<forall> n2. d |\<in>| D \<longrightarrow> (( (n2 > N \<longrightarrow> P a b c d n2))))))))"
      by simp  
    hence "(\<And> a   . a |\<in>| A \<Longrightarrow> (\<exists> N.  (\<forall> b. b|\<in>|B \<longrightarrow>  (\<forall> c. c |\<in>| C \<longrightarrow>(\<forall> n2.  (\<forall> d .d |\<in>| D \<longrightarrow> (( (n2 > N \<longrightarrow> P a b c d n2)))))))))"
      by metis  
    hence "(\<And> a   . a |\<in>| A \<Longrightarrow> (\<exists> N.  (\<forall> b. b|\<in>|B \<longrightarrow>  (\<forall> n2. (\<forall> c. c |\<in>| C \<longrightarrow>( (\<forall> d .d |\<in>| D \<longrightarrow> (( (n2 > N \<longrightarrow> P a b c d n2))))))))))"
      by metis
    hence "(\<And> a   . a |\<in>| A \<Longrightarrow> (\<exists> N. (\<forall> n2. (\<forall> b. b|\<in>|B \<longrightarrow>   (\<forall> c. c |\<in>| C \<longrightarrow>( (\<forall> d .d |\<in>| D \<longrightarrow> (( (n2 > N \<longrightarrow> P a b c d n2))))))))))"
      by metis
    hence "(\<And> a   . a |\<in>| A \<Longrightarrow> (\<exists> N. (\<forall> n2. (n2 > N \<longrightarrow>(\<forall> b. b|\<in>|B \<longrightarrow>   (\<forall> c. c |\<in>| C \<longrightarrow>( (\<forall> d .d |\<in>| D \<longrightarrow> ((  P a b c d n2))))))))))"
      by metis
    then have n6787 : "(\<And> a   . a |\<in>| A \<Longrightarrow> (\<exists> N. (\<forall> n2 . (n2 > N \<longrightarrow>  (\<forall> b. b|\<in>|B \<longrightarrow>  (\<forall> c. c |\<in>| C \<longrightarrow> (\<forall> d . d |\<in>| D \<longrightarrow> (P a b c d n2))))))))" by auto
    def Q == "\<lambda> a n2. (\<forall> b. b|\<in>|B \<longrightarrow>  (\<forall> c. c |\<in>| C \<longrightarrow> (\<forall> d . d |\<in>| D \<longrightarrow> (P a b c d n2))))"
    then have "(\<And> a   . a |\<in>| A \<Longrightarrow> (\<exists> N.(\<forall> n2 . (n2 > N \<longrightarrow>  Q a n2))))" using n6787 by blast 
    then have "\<exists> N. (\<forall>    a   .  a|\<in>|A \<longrightarrow>((\<forall> n2 . (n2 > N \<longrightarrow> Q a n2))))" using n54687a  by auto
    then show "(\<exists> N. (\<forall> a . (a |\<in>| A \<longrightarrow> (\<forall> b. b|\<in>|B \<longrightarrow>  (\<forall> c. c |\<in>| C \<longrightarrow> (\<forall> d . d |\<in>| D \<longrightarrow> ((\<forall> n2 . (n2 > N \<longrightarrow> P a b c d n2)))))))))" using Q_def by blast
  qed
  then show "\<exists> N. (\<forall> a b c d . a |\<in>| A \<longrightarrow> b|\<in>|B \<longrightarrow> c |\<in>| C \<longrightarrow> d |\<in>| D \<longrightarrow> ((\<forall> n2 . (n2 > N \<longrightarrow> P a b c d n2))))" by auto
      
qed
  
  
    
  
  
lemma piDeltaPhi :
  shows "(\<Pi>\<^sub>\<phi> (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) s)) = (\<Pi>\<^sub>\<delta> (\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) s))" 
proof
  show "\<Pi>\<^sub>\<phi> (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) s) \<subseteq> UNION ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> \<circ> \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i)) s) fset" using pathsForForestLanguage_def  by (smt Collect_mono Union_eq comp_apply image_eqI notin_fset) 
  show "UNION ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> \<circ> \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i)) s) fset \<subseteq> \<Pi>\<^sub>\<phi> (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) s)" using pathsForForestLanguage_def  by (smt Collect_mono UNION_eq imageE notin_fset o_apply)
qed
  
          
  
lemma plusUplusD :
  assumes "\<And>x . (x |\<in>| totalForests \<Longrightarrow> (\<Union>| (\<Pi> |`| (x))) \<in> ( (((\<Uplus>\<^sub>\<delta> ( ((\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> aut) |`| Sa1)))))))"
  assumes "totalForest == \<Union>|  totalForests"
    shows "\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest \<in> ( (((\<Uplus>\<^sub>\<delta> ( ((\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> aut) |`| Sa1))))))" 
proof -                                     
  
  have "(\<forall> tr  . tr |\<in>| (\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest) \<longrightarrow> (\<exists> lang . lang |\<in>| (((\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> aut) |`| Sa1)) \<and> (\<exists> (subforest ) . (tr |\<in>| subforest \<and> subforest |\<subseteq>| (\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest) \<and> subforest \<in> lang)))) "
  proof 
    
    show "(\<And> tr  . tr |\<in>| (\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest) \<longrightarrow> (\<exists> lang . lang |\<in>| (((\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> aut) |`| Sa1)) \<and> (\<exists> (subforest ) . (tr |\<in>| subforest \<and> subforest |\<subseteq>| (\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest) \<and> subforest \<in> lang))))"
    proof 
      show "(\<And> tr  . tr |\<in>| (\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest) \<Longrightarrow> (\<exists> lang . lang |\<in>| (((\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> aut) |`| Sa1)) \<and> (\<exists> (subforest ) . (tr |\<in>| subforest \<and> subforest |\<subseteq>| (\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest) \<and> subforest \<in> lang))))"
        proof -
    fix path
    assume "path |\<in>| (\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest)"
    then obtain tr where "tr |\<in>| totalForest" and "path |\<in>| \<Pi> tr" using pathsInForest_def using pathsTreeForest by blast 
    then obtain forest where ny66788 : "forest |\<in>| totalForests" and "tr |\<in>| forest" using assms(2)    by auto 
    then have "(\<Union>| (\<Pi> |`| (forest))) \<in> ( (((\<Uplus>\<^sub>\<delta> ( ((\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> aut) |`| Sa1))))))" using assms(1) by auto
    then have a6587 : "\<And> tr . tr |\<in>| (\<Union>| (\<Pi> |`| (forest))) \<Longrightarrow> (\<exists> lang . lang |\<in>| (  ((\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> aut) |`| Sa1)) \<and> (\<exists> (subforest) . (tr |\<in>| subforest \<and> subforest |\<subseteq>| (\<Union>| (\<Pi> |`| (forest))) \<and> subforest \<in> lang)))" using biguplusForestsD_def by blast
    have "path |\<in>| (\<Union>| (\<Pi> |`| (forest)))"     using \<open>path |\<in>| \<delta>\<^sub>\<tau> tr\<close> \<open>tr |\<in>| forest\<close> by blast 
        
    then have "(\<exists> lang . lang |\<in>| (  ((\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> aut) |`| Sa1)) \<and> (\<exists> (subforest) . (path |\<in>| subforest \<and> subforest |\<subseteq>| (\<Union>| (\<Pi> |`| (forest))) \<and> subforest \<in> lang)))" using a6587 by auto
    then obtain lang where "lang |\<in>| (  ((\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> aut) |`| Sa1))" and "(\<exists> (subforest) . (path |\<in>| subforest \<and> subforest |\<subseteq>| (\<Union>| (\<Pi> |`| (forest))) \<and> subforest \<in> lang))" by auto
    then obtain subforest where "lang |\<in>| (  ((\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> aut) |`| Sa1))" and " (path |\<in>| subforest)" and n6798 : " subforest |\<subseteq>| (\<Union>| (\<Pi> |`| (forest)))" and "subforest \<in> lang" by auto
        
        
    from n6798 assms(2) pathsInForest_def  ny66788 have "(\<Union>| (\<Pi> |`| (forest))) |\<subseteq>| (\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest)"       by (simp add: pathsInForest_def ffUnion_upper fimage_mono) 
    then have "subforest |\<subseteq>|\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest" using n6798 by auto
        
        
    then have "lang |\<in>| (((\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> aut) |`| Sa1)) \<and> (\<exists> (subforest ) . (path |\<in>| subforest \<and> subforest |\<subseteq>| (\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest) \<and> subforest \<in> lang))"  using \<open>lang |\<in>| (op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> \<circ> \<L>\<^sub>\<phi>\<^sub>\<sigma> aut) |`| Sa1\<close> \<open>path |\<in>| subforest\<close> \<open>subforest \<in> lang\<close> by auto
        
    then have "(\<exists> lang . lang |\<in>| (((\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> aut) |`| Sa1)) \<and> (\<exists> (subforest ) . (path |\<in>| subforest \<and> subforest |\<subseteq>| (\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest) \<and> subforest \<in> lang)))" by auto
    then show "(\<exists> lang . lang |\<in>| (((\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> aut) |`| Sa1)) \<and> (\<exists> (subforest ) . (path |\<in>| subforest \<and> subforest |\<subseteq>| (\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest) \<and> subforest \<in> lang)))" by auto
  qed
qed
qed
then show "\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest \<in> ( (((\<Uplus>\<^sub>\<delta> ( ((\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> aut) |`| Sa1))))))" using biguplusForestsD_def by blast
qed
  
        
        

        
    
lemma psiSigmaDClosedUnderPlus0 :
  fixes totalForestForPath totalForests
  fixes forest
    fixes Sa1 Sa2
  defines "totalForest == \<Union>|  totalForests"
    assumes "\<And>x . (x |\<in>| totalForests \<Longrightarrow> (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  x) \<in> (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2))" 
    shows "\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest \<in> (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2)" 
proof -
  from assms(2) have n766787 : "\<And>x . (x |\<in>| totalForests \<Longrightarrow> (\<Union>| (\<Pi> |`| (x))) \<in> (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2))"   using pathsInForest_def by metis
  then have  "\<And>x . (x |\<in>| totalForests \<Longrightarrow> (\<Union>| (\<Pi> |`| (x))) \<in> ( (((\<Uplus>\<^sub>\<delta> ( ((\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1) |`| Sa1)))))))" using n766787 \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta>_def  by auto
  then have n76898 : "\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest \<in> ( (((\<Uplus>\<^sub>\<delta> ( ((\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1) |`| Sa1))))))"  using assms  using plusUplusD by blast  
  from n766787 have  "\<And>x . (x |\<in>| totalForests \<Longrightarrow> (\<Union>| (\<Pi> |`| (x))) \<in> ( (((\<Uplus>\<^sub>\<delta> ( ((\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2) |`| Sa2)))))))" using n766787 \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta>_def  by auto
  then have n657 : "\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest \<in> ( (((\<Uplus>\<^sub>\<delta> ( ((\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2) |`| Sa2))))))"  using assms  using plusUplusD by blast  
  from n76898 n657 show "\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest \<in> (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2)" using \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta>_def by blast
qed
  
  
  
lemma psiSigmaDClosedUnderPlus :
  fixes totalForestForPath
  fixes forest
    fixes Sa1 Sa2
  defines "totalForest == \<Union>|  (totalForestForPath  |`| (\<Pi> ( forest)))"
    assumes "\<And>x . (x |\<in>| \<Pi> ( forest) \<Longrightarrow> (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  (totalForestForPath x)) \<in> (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2))" 
    shows "\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest \<in> (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2)" 
using psiSigmaDClosedUnderPlus0 using assms(2) totalForest_def by blast
  
    
      
lemma constantLemma :
  fixes s
  fixes Sa1
  fixes Sa2
  fixes i
  assumes y1 : "((s |\<in>| (state_set) (\<A> i)))"
  assumes y2 : "(( Sa1 |\<subseteq>| (state_set) \<A>\<^sub>1))"
  assumes y3 : "(( Sa2 |\<subseteq>| (state_set) \<A>\<^sub>2))"
  shows "\<exists> N. constantIsSuitableForStates i s Sa1 Sa2 N"
proof -
  def auti == "\<A> i"
  def LSa == "(\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta>  Sa1 Sa2)"
  def LS == "\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> auti s"
  def I == "(\<Pi>\<^sub>\<delta> LS) - (\<Pi>\<^sub>\<delta> LSa)"
  have 0 : "I \<in> \<I>" 
  proof -
    from y1 y2 y3 auti_def LSa_def LS_def obtain setPair where y4 : "(
                              (*  (((s |\<in>| (state_set) (\<A> i))) \<and> ((( Sa1 |\<subseteq>| (state_set) \<A>\<^sub>1))) \<and> (( Sa2 |\<subseteq>| (state_set) \<A>\<^sub>2)) \<and>*)
                                (\<pi>\<^sup>1 setPair = (\<Pi>\<^sub>\<phi> (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) s))) 
                              \<and> (\<pi>\<^sup>2 setPair = UNION (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2) fset))" by (meson fst_conv snd_conv)
    from auti_def y4 I_def LSa_def LS_def piDeltaPhi have y5 : "I = (\<lambda>pair . \<pi>\<^sup>1 pair - \<pi>\<^sup>2 pair) setPair" by auto
    from y4   have "\<exists>i Sa1 Sa2 s. \<pi>\<^sup>1 setPair = \<Pi>\<^sub>\<phi> (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) s) \<and> \<pi>\<^sup>2 setPair = UNION (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2) fset" by auto
    then show "I \<in> \<I>"  using \<I>_def      by (simp add: \<I>_def y5)
  qed
  have n545688 : "(\<not> ( ( (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) s) \<Turnstile> I))) \<Longrightarrow> (\<exists>n. (\<forall> n2 . (n2 \<ge> n \<longrightarrow> (realizedIn (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) s) (UNION (fset (\<Z>\<^sub>\<delta> n2 (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2))) fset)))))"
  proof -
    assume "\<not> ( ( (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) s) \<Turnstile> I))"
    then obtain forest where a7 : "forest \<in> ( ( (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) s)))" and a8 : "(fset (\<Pi> forest)) \<inter> I = {}"       using entails_altdef by blast
    have n65687a : "(fset (\<Pi> ( forest))) \<subseteq> \<Pi>\<^sub>\<delta> (\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) s)"
    proof -
      from a7 have  a7 : "forest \<in> ( ( (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) s)))" by auto
      hence a8 : "(finsert forest {||}) \<in> ( \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) s)"           by (simp add: forest_language_for_state_def language_for_state_def) 
      hence a78775 : "\<Pi>\<^sub>\<iota>\<^sub>\<phi> (finsert forest {||}) \<in> (\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) s)  "           by auto   
      have "\<Pi>\<^sub>\<iota>\<^sub>\<phi> (finsert forest {||}) = \<Pi> ( forest)" (*using pathsInForest_def *)
      proof
        fix x
        show "\<Pi>\<^sub>\<iota>\<^sub>\<phi> {|forest|} |\<subseteq>| \<delta>\<^sub>\<tau> forest" using pathsInForest_def          by (metis fsingleton_iff fsubsetI pathsTreeForest)
        show "\<delta>\<^sub>\<tau> forest |\<subseteq>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> {|forest|} "  using pathsInForest_def          by (metis fsingleton_iff fsubsetI pathsTreeForest)
      qed
      hence "\<Pi> ( forest) \<in> (\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) s)  "    using a78775    by auto
      then show "(fset (\<Pi> ( forest))) \<subseteq> \<Pi>\<^sub>\<delta> (\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) s)  "               by blast
    qed
    have n65687 : "(fset (\<Pi> forest)) \<subseteq> \<Pi>\<^sub>\<delta> LS"
    proof 
      fix x
      assume n56898 : "x \<in> fset (\<delta>\<^sub>\<tau> forest)"
      from n65687a have "(fset (\<Pi> ( forest))) \<subseteq> \<Pi>\<^sub>\<delta> (\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) s)  "               by blast
      hence "x \<in> \<Pi>\<^sub>\<delta> (\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) s)  " using n56898  by auto
      then show "x \<in> \<Pi>\<^sub>\<delta> LS" using LS_def auti_def by auto
    qed
    then have n65489 : "(fset (\<Pi> forest)) \<subseteq> \<Pi>\<^sub>\<delta> LSa" using I_def a8 by blast
    show " \<exists>n. (\<forall> n2 . (n2 \<ge> n \<longrightarrow> (realizedIn (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) s) (UNION (fset (\<Z>\<^sub>\<delta> n2 (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2))) fset))))"
    proof -
        fix n
        from realizedIn_def have "((realizedIn (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) s)   (\<Pi>\<^sub>\<delta> (fset (\<Z>\<^sub>\<delta> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2) )))) = (\<exists>\<gg>. \<gg> \<in> (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) s) \<and> fset (\<Pi> \<gg>) \<subseteq> (\<Pi>\<^sub>\<delta> (fset (\<Z>\<^sub>\<delta> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2) )))))" by auto
        from a7 have  a7 : "forest \<in> ( ( (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) s)))" by auto
        from n65687a  have "(fset (\<Pi> ( forest))) \<subseteq> \<Pi>\<^sub>\<delta> (\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) s)" by auto
        have n54568 : "\<exists> fullHeight . (\<forall> path . (path |\<in>| (\<Pi> ( forest)) \<longrightarrow> (\<forall> n2 . n2 \<ge> fullHeight \<longrightarrow> (path \<in> (\<Pi>\<^sub>\<delta> (fset (\<Z>\<^sub>\<delta> n2 (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2) )))))))"
        proof -
          from n65687a notin_fset n65489 LSa_def    have n8768 : "\<And>path. path |\<in>| (\<Pi> ( forest)) \<Longrightarrow> path \<in> UNION (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2) fset" by (metis (no_types, lifting) subsetCE) 
          have n656787 : "\<And>path. path |\<in>| (\<Pi> ( forest)) \<Longrightarrow> (\<exists> pathsetForPath . (path |\<in>| (pathsetForPath ) \<and> (pathsetForPath ) \<in> (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2)))" using notin_fset  n8768   UN_iff               by (metis (full_types)) 
          def pathsetForPath == "\<lambda> path. (SOME pathset. (path |\<in>| pathset \<and> pathset \<in> (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2)))"
          have n7687 : "\<And>path. path |\<in>| (\<Pi> ( forest)) \<Longrightarrow> (path |\<in>| (pathsetForPath path) \<and> (pathsetForPath path) \<in> (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2))" using n656787 pathsetForPath_def    by (smt someI_ex) 
          have a90 : "\<And> path tr . path |\<in>| (\<Pi> ( forest)) \<Longrightarrow> tr |\<in>| (pathsetForPath path) \<Longrightarrow> (\<exists> lang . lang |\<in>| ( ((\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1) |`| Sa1)) \<and> (\<exists> (subforest) . (tr |\<in>| subforest \<and> subforest |\<subseteq>| (pathsetForPath path) \<and> subforest \<in> lang)))"
          proof -
            fix path
            assume n767898 : "path |\<in>| (\<Pi> ( forest))"
            def pathset == "pathsetForPath path"
            from n7687 n767898 pathset_def  have a20 : "path |\<in>| pathset" and a21 : "pathset \<in> (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2)"     by auto
            from a21 have "\<And>path. path |\<in>| (\<Pi> ( forest)) \<Longrightarrow> pathset \<in> ( (((\<Uplus>\<^sub>\<delta> ( ((\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1) |`| Sa1)))))) " using \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta>_def by auto
            hence "\<And> tr . tr |\<in>| pathset \<Longrightarrow> (\<exists> lang . lang |\<in>| ( ((\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1) |`| Sa1)) \<and> (\<exists> (subforest) . (tr |\<in>| subforest \<and> subforest |\<subseteq>| pathset \<and> subforest \<in> lang)))" using biguplusForestsD_def           by (smt IntE \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta>_def a21 mem_Collect_eq) 
            then show "\<And>  tr .   tr |\<in>| (pathsetForPath path) \<Longrightarrow> (\<exists> lang . lang |\<in>| ( ((\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1) |`| Sa1)) \<and> (\<exists> (subforest) . (tr |\<in>| subforest \<and> subforest |\<subseteq>| (pathsetForPath path) \<and> subforest \<in> lang)))" using pathset_def by auto
          qed
          def pathsetForEachPath == "\<lambda> path tr. (SOME  subforest. (\<exists> lang . lang |\<in>| ( ((\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1) |`| Sa1)) \<and> ( (tr |\<in>| subforest \<and> subforest |\<subseteq>| (pathsetForPath path) \<and> subforest \<in> lang))))"
          have n8775 : "\<And>path tr . path |\<in>| (\<Pi> ( forest)) \<Longrightarrow>tr |\<in>| (pathsetForPath path) \<Longrightarrow> (\<exists> lang . lang |\<in>| ( ((\<delta>\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1) |`| Sa1)) \<and> ((tr |\<in>| (pathsetForEachPath path tr) \<and> (pathsetForEachPath path tr) |\<subseteq>| (pathsetForPath path) \<and> (pathsetForEachPath path tr) \<in> lang)))" using a90 pathsetForEachPath_def              by (smt someI_ex) 
          hence n6798 : "\<And>path tr . path |\<in>| (\<Pi> ( forest)) \<Longrightarrow>tr |\<in>| (pathsetForPath path) \<Longrightarrow> (\<exists> forest . \<exists> lang . \<Pi>\<^sub>\<iota>\<^sub>\<phi> forest = (pathsetForEachPath path tr) \<and> forest \<in> lang \<and> lang |\<in>| ( ((\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1) |`| Sa1)))"  by fastforce  
          def forestsForEachPath == "\<lambda> path tr . (SOME forest. (\<exists> lang . \<Pi>\<^sub>\<iota>\<^sub>\<phi> forest = (pathsetForEachPath path tr) \<and> forest \<in> lang \<and> lang |\<in>| ( ((\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1) |`| Sa1))))"
          then have n657897 : "\<And>path tr . path |\<in>| (\<Pi> ( forest)) \<Longrightarrow> tr |\<in>| (pathsetForPath path) \<Longrightarrow> ( \<exists> lang . \<Pi>\<^sub>\<iota>\<^sub>\<phi> (forestsForEachPath path tr) = (pathsetForEachPath path tr) \<and> (forestsForEachPath path tr) \<in> lang \<and> lang |\<in>| ( ((\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1) |`| Sa1)))" using n6798        by (smt someI_ex) 
          have n7698 : "\<And>path . path |\<in>| (\<Pi> ( forest)) \<Longrightarrow> (\<exists>  totalForest .(pathsetForPath path = \<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest \<and>  (\<exists> heightForForest .((\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest \<in> (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2)) \<and> (\<forall> t n2. t |\<in>| totalForest \<longrightarrow> heightForForest \<le> n2 \<longrightarrow> height t \<le>  n2)))))"
          proof -
            fix path
            assume "path |\<in>| (\<Pi> ( forest))"
            def pathset == "pathsetForPath path"
            def totalForest == "\<Union>| ((forestsForEachPath path) |`| pathset)"
            def totalForestPathset == "\<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Union>| ((forestsForEachPath path) |`| pathset))"
            have n657o98 : "totalForestPathset = pathset" proof
              show "totalForestPathset |\<subseteq>| pathset" 
              proof
                fix x
                assume " x |\<in>| totalForestPathset "
                then obtain oldTree where "oldTree |\<in>| (\<Union>| ((forestsForEachPath path) |`| pathset))" and "x |\<in>| \<Pi> oldTree" using totalForestPathset_def               using pathsTreeForest by blast
                then obtain path2 where "path2 |\<in>| pathset" and "oldTree |\<in>| ((forestsForEachPath path)  path2)"               by auto 
                then show "x |\<in>| pathset" using n8775      \<open>x |\<in>| \<delta>\<^sub>\<tau> oldTree\<close> less_eq_fset.rep_eq n657897 notin_fset pathsTreeForest subsetCE               by (smt \<open>path |\<in>| \<delta>\<^sub>\<tau> forest\<close> fset_mp pathset_def) 
              qed
              show "pathset |\<subseteq>| totalForestPathset"
              proof 
                fix x
                assume n87789 : " x |\<in>| pathset"
                hence "x |\<in>| ((pathsetForEachPath path) x)" using n8775               using \<open>path |\<in>| \<delta>\<^sub>\<tau> forest\<close> pathset_def by blast 
                then show "x |\<in>| totalForestPathset" using n87789 totalForestPathset_def      ffUnionI fimage_eqI n657897 pathsTreeForest               by (metis \<open>path |\<in>| \<delta>\<^sub>\<tau> forest\<close> pathset_def)
              qed
            qed
            then have n876765 : "(\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest \<in> (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2))" using  totalForestPathset_def totalForest_def           by (simp add: \<open>path |\<in>| \<delta>\<^sub>\<tau> forest\<close> n7687 pathset_def) 
            def heightForForest == "maxFset (height |`| totalForest)"
            have "\<And>t . t |\<in>| totalForest \<Longrightarrow> height t \<le> heightForForest" using heightForForest_def finiteMaxExists(1) by simp
            have n545787 : "\<And>t n2 . t |\<in>| totalForest \<Longrightarrow> heightForForest \<le> n2 \<Longrightarrow> height t \<le>  n2" using heightForForest_def finiteMaxExists(1)                 using \<open>\<And>ta. ta |\<in>| totalForest \<Longrightarrow> height ta \<le> heightForForest\<close> dual_order.trans by blast 
            from n876765 n545787 n657o98 totalForest_def totalForestPathset_def show "(\<exists>  totalForest .(pathsetForPath path = \<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest \<and>  (\<exists> heightForForest .((\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest \<in> (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2)) \<and> (\<forall> t n2. t |\<in>| totalForest \<longrightarrow> heightForForest \<le> n2 \<longrightarrow> height t \<le>  n2)))))"             by (metis pathset_def)
          qed
          def isGood == "\<lambda> (path :: abc list) totalForest .(pathsetForPath path = \<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest \<and> (\<exists> heightForForest .((\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest \<in> (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2)) \<and> (\<forall> t n2. t |\<in>| totalForest \<longrightarrow> heightForForest \<le> n2 \<longrightarrow> height t \<le>  n2))))"
          from n7698 have n7698b : "\<And>path . path |\<in>| (\<Pi> ( forest)) \<Longrightarrow> (\<exists>  totalForest .isGood path totalForest)" using isGood_def by auto
          def totalForestForPath ==   "\<lambda> (path :: abc list) .(SOME totalForest. isGood path totalForest)"
          from n7698 totalForestForPath_def            have n545787 : "\<And>(path :: abc list) . path |\<in>| (\<Pi> ( forest)) \<Longrightarrow> isGood path (totalForestForPath path)" using someI_ex    by (simp add: someI_ex n7698b) 
          then have n659 : "\<And>(path :: abc list) . path |\<in>| (\<Pi> ( forest)) \<Longrightarrow> ((\<exists> heightForForest .(((\<forall> t n2. t |\<in>|  (totalForestForPath path) \<longrightarrow> heightForForest \<le> n2 \<longrightarrow> height t \<le>  n2)))))" using isGood_def by blast
          def totalForest == "\<Union>|  (totalForestForPath  |`| (\<Pi> ( forest)))"
          have "\<Pi> ( forest) |\<subseteq>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest" 
          proof
            fix x
            assume "x |\<in>| \<Pi> ( forest)"
            hence "x |\<in>| (pathsetForPath  x)"            by (simp add: n7687)
            hence "x |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi>  (totalForestForPath x)"                using \<open>x |\<in>| \<delta>\<^sub>\<tau> forest\<close> isGood_def n545787 by auto
            then show "x |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest"                by (metis \<open>x |\<in>| \<delta>\<^sub>\<tau> forest\<close> ffUnionI fimage_eqI pathsTreeForest totalForest_def) 
          qed
          have n54e7 :  "\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest \<in> (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2)" 
          proof -
            have "\<And>x . x |\<in>| \<Pi> ( forest) \<Longrightarrow> (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  (totalForestForPath x)) \<in> (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2)"                  using isGood_def n545787 by blast
            then show "\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest \<in> (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2)" using totalForest_def psiSigmaDClosedUnderPlus by blast
          qed
          def heightIsGood == "\<lambda> path heightForForest . (\<forall> t n2. t |\<in>| (totalForestForPath path) \<longrightarrow> heightForForest \<le> n2 \<longrightarrow> height t \<le>  n2)"
          from n659 heightIsGood_def have n546898 : "\<And>(path :: abc list) . path |\<in>| (\<Pi> ( forest)) \<Longrightarrow> (\<exists> heightForForest. heightIsGood path heightForForest)" by auto
          def sufficientHeights == "\<lambda> path. (SOME heightForForest.(heightIsGood path heightForForest))"
          from n546898 sufficientHeights_def n659  have n56898 : "\<And>(path :: abc list) . path |\<in>| (\<Pi> ( forest)) \<Longrightarrow> (heightIsGood path (sufficientHeights path))" using someI_ex by (simp add: someI_ex)
          def goodHeight == "maxFset (sufficientHeights |`| (\<Pi> ( forest)))"
          from goodHeight_def finiteMaxExists(1) totalForest_def n56898 heightIsGood_def have "(((\<forall> t n2. t |\<in>|  (totalForest) \<longrightarrow> goodHeight \<le> n2 \<longrightarrow> height t \<le>  n2)))"  by (smt ffUnionLemma fimageE fimage_eqI le_trans)
          hence "\<And> n2 .goodHeight \<le> n2 \<Longrightarrow>totalForest \<in> (fset (boundedForests  n2))" using  restrictionIsFiniteForests   by blast
          hence "\<And> n2 .goodHeight \<le> n2 \<Longrightarrow>totalForest |\<in>| ((boundedForests  n2))" using   notin_fset               by fastforce  
          then have "\<And> n2 .goodHeight \<le> n2 \<Longrightarrow> (\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest) |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| (inf_fset2 (boundedForests n2) {f . (\<Pi>\<^sub>\<iota>\<^sub>\<phi> f \<in> (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2))} )"  using n54e7
          proof -
            fix n2 :: nat
            assume a1: "goodHeight \<le> n2"
            have "\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest \<in> \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2"
              by (metis \<open>\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest \<in> \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2\<close>)
            then have f2: "totalForest \<in> {f. \<Pi>\<^sub>\<iota>\<^sub>\<phi> f \<in> \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2}"
              by blast
            have "totalForest |\<in>| boundedForests n2"
              using a1 \<open>\<And>n2. goodHeight \<le> n2 \<Longrightarrow> totalForest |\<in>| boundedForests n2\<close> by auto
            then show "\<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| inf_fset2 (boundedForests n2) {f. \<Pi>\<^sub>\<iota>\<^sub>\<phi> f \<in> \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2}"
              using f2 by blast
          qed
          then have " (\<forall> path . (path |\<in>| (\<Pi> ( forest)) \<longrightarrow> (\<forall> n2 . n2 \<ge> goodHeight \<longrightarrow> (path \<in> (\<Pi>\<^sub>\<delta> (fset (\<Z>\<^sub>\<delta> n2 (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2) )))))))"             by (metis Collect_cong \<Z>\<^sub>\<delta>_def \<open>\<delta>\<^sub>\<tau> forest |\<subseteq>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> totalForest\<close> ffUnion.rep_eq ffUnionI fset_mp notin_fset)
          then show "\<exists> fullHeight . (\<forall> path . (path |\<in>| (\<Pi> ( forest)) \<longrightarrow> (\<forall> n2 . n2 \<ge> fullHeight \<longrightarrow> (path \<in> (\<Pi>\<^sub>\<delta> (fset (\<Z>\<^sub>\<delta> n2 (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2) )))))))" by auto
        qed
        def fullHeight == "SOME fullHeight. ((\<forall> path . (path |\<in>| (\<Pi> ( forest)) \<longrightarrow> (\<forall> n2 . n2 \<ge> fullHeight \<longrightarrow> (path \<in> (\<Pi>\<^sub>\<delta> (fset (\<Z>\<^sub>\<delta> n2 (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2) ))))))))"
        hence "(\<And> path . (path |\<in>| (\<Pi> ( forest)) \<Longrightarrow> (\<And> n2 . n2 \<ge> fullHeight \<Longrightarrow> (path \<in> (\<Pi>\<^sub>\<delta> (fset (\<Z>\<^sub>\<delta> n2 (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2) )))))))" using n54568 someI_ex  LSa_def   by smt
        then have "(\<And> n2 . n2 \<ge> fullHeight \<longrightarrow> fset (\<Pi> forest) \<subseteq> (UNION (fset (\<Z>\<^sub>\<delta> n2 (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2))) fset))"          by (meson notin_fset subsetI)
        then have "(\<And> n2 . n2 \<ge> fullHeight \<longrightarrow> (realizedIn (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) s) (UNION (fset (\<Z>\<^sub>\<delta> n2 (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2))) fset)))"          using a7 realizedIn_def
        proof -
          fix n2 :: nat
          { assume "\<exists>t. t \<in> \<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) s \<and> fset (\<delta>\<^sub>\<tau> t) \<subseteq> UNION (fset (\<Z>\<^sub>\<delta> n2 (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2))) fset"
            then have "fullHeight \<le> n2 \<longrightarrow> realizedIn (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) s) (UNION (fset (\<Z>\<^sub>\<delta> n2 (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2))) fset)"              by (meson realizedIn_def) }
          then show "fullHeight \<le> n2 \<longrightarrow> realizedIn (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) s) (UNION (fset (\<Z>\<^sub>\<delta> n2 (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2))) fset)"            using \<open>\<And>n2. fullHeight \<le> n2 \<longrightarrow> fset (\<delta>\<^sub>\<tau> forest) \<subseteq> UNION (fset (\<Z>\<^sub>\<delta> n2 (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2))) fset\<close> a7 by blast
        qed 
        then show " \<exists>n. (\<forall> n2 . (n2 \<ge> n \<longrightarrow> (realizedIn (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) s) (UNION (fset (\<Z>\<^sub>\<delta> n2 (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2))) fset))))" by auto
    qed
  qed
  then have n545688b : " \<exists>n. ((\<not> \<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) s \<Turnstile> I) \<longrightarrow> (\<forall>n2\<ge>n. realizedIn (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) s) (UNION (fset (\<Z>\<^sub>\<delta> n2 (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2))) fset)))" by blast
  def constantForStates == "SOME n. ((\<not> \<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) s \<Turnstile> I) \<longrightarrow> (\<forall>n2\<ge>n. realizedIn (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) s) (UNION (fset (\<Z>\<^sub>\<delta> n2 (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2))) fset)))"
  from n545688b constantForStates_def have n65687 : " ((\<not> \<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) s \<Turnstile> I) \<longrightarrow> (\<forall>n2\<ge>constantForStates. realizedIn (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) s) (UNION (fset (\<Z>\<^sub>\<delta> n2 (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2))) fset)))" using someI_ex by smt
  hence n65687b : "(\<And>n2. n2 \<ge>constantForStates \<Longrightarrow> ( ((\<not> \<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) s \<Turnstile> I) \<Longrightarrow> realizedIn (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) s) (UNION (fset (\<Z>\<^sub>\<delta> n2 (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2))) fset))))" by auto
      have n545787 : "((I \<inter> \<Pi>\<^sub>\<delta> ( (( \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2  )))) = {})"        using I_def LSa_def by blast
  have "(((\<And> n . ((Suc n > constantForStates) \<Longrightarrow> ((\<not>(realizedIn    (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) s)      (\<Pi>\<^sub>\<delta> (fset (\<Z>\<^sub>\<delta> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2) ))) ) )   \<Longrightarrow> ( ( ( (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) s) \<Turnstile> I)  \<and> ((I \<inter> \<Pi>\<^sub>\<delta> ( (( \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2  )))) = {}))))))))" using n545787 n65687b by auto
  then have "constantIsSuitableForStates i s Sa1 Sa2 constantForStates" using constantIsSuitableForStates_def 0 by auto
  then show "\<exists> N. constantIsSuitableForStates i s Sa1 Sa2 N" by auto
qed
    
  
  
  
  
  
  
lemma greaterConstantsAreGood :
  fixes s
  fixes Sa1
  fixes Sa2
  fixes i
  assumes "((s |\<in>| (state_set) (\<A> i)))"
  assumes "(( Sa1 |\<subseteq>| (state_set) \<A>\<^sub>1))"
  assumes "(( Sa2 |\<subseteq>| (state_set) \<A>\<^sub>2))"
  fixes n
  fixes N
  assumes "constantIsSuitableForStates i s Sa1 Sa2 N"
  assumes "n > N"
  shows "constantIsSuitableForStates i s Sa1 Sa2 n"
  by (meson assms constantIsSuitableForStates_def less_trans)
    
    
    
    
lemma n67789564 : 
              assumes "(x |\<in>| (fimage f ((\<Union>| (fimage g h)))))"
              obtains child where "child |\<in>| h" and "x |\<in>| (fimage f (g child))"
  using assms by auto
                
    
    
definition realizesUniv where "realizesUniv n = (\<forall> i \<alpha> r n2. (Suc n2 > n \<longrightarrow> (r |\<in>| rule_set (\<A> i) \<longrightarrow> symbol r = \<alpha> \<longrightarrow> (realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) r) (\<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> n2 UNIV) \<union> {[]}))))))"
  
  
lemma pathsSingeton :
  shows "\<Pi>\<^sub>\<iota>\<^sub>\<phi> (finsert tr {||}) = \<Pi> tr"
proof
  show " \<Pi>\<^sub>\<iota>\<^sub>\<phi> {|tr|} |\<subseteq>| \<Pi> tr"  using pathsInForest_def    by (metis fsingleton_iff fsubsetI pathsTreeForest)
      show "\<Pi> tr |\<subseteq>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> {|tr|} " using pathsInForest_def    by (metis fsingleton_iff fsubsetI pathsTreeForest)
  qed
  
  
lemma rootRule :
  assumes "tr \<in> ((\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) rule))"
  shows  "symbol rule = root tr"
  by (metis assms language_for_rule_def mem_Collect_eq tree_for_rule_def) 
    
    
lemma  commuteExistsAll3 : "\<And> (D :: 'a fset) (P :: 'a \<Rightarrow> nat \<Rightarrow> bool) . ((\<And>d. d |\<in>| D \<Longrightarrow> \<exists>n. \<forall>n2>n. P (d :: 'a) n2) \<Longrightarrow> \<exists>N. \<forall>d. d |\<in>| D \<longrightarrow> (\<forall>n2>N. P d n2))"
  using commuteExistsAll by blast
  
    
    
lemma realizedInUniv1:
  assumes rulesLangsNonempty : "\<And> \<R> i r . (r |\<in>| rule_set (\<A> i) \<Longrightarrow>  ((\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) r)  \<noteq> {}))"
  shows "\<exists> n . realizesUniv n"
proof -
  def heightPerRule == "\<lambda> i . \<lambda> rule . (SOME goodHeight . ( (realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) rule) ((symbol rule) \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> goodHeight UNIV) \<union> {[]})))))"
  have n6567987 : "\<And>i rule . (rule |\<in>| rule_set (\<A> i) \<Longrightarrow> (\<exists> goodHeight.(\<forall> ht.(ht > goodHeight \<longrightarrow>  (realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) rule) ((symbol rule) \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> ht UNIV) \<union> {[]})))))))"
  proof -
    fix i rule
    assume "rule |\<in>| rule_set (\<A> i)"
    then obtain tr where n1 : "tr \<in> ((\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) rule))" using assms        by auto
    def forest == "(finsert tr {||})"
    have n65687 : "forest \<in> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) rule)" using n1 forest_def by (simp add: forest_language_for_rule_def language_for_rule_def) 
    def goodHeight == "height tr"
    have "\<And> ht child. ht > goodHeight \<Longrightarrow> child |\<in>| childrenSet tr \<Longrightarrow> child |\<in>| \<Z>\<^sub>\<tau> ht UNIV" using Z_def \<Z>\<tau>_lemma goodHeight_def heightOfChild notin_fset by fastforce 
        
        
        
    have n7588 : "\<And> ht child. ht > goodHeight \<Longrightarrow> child |\<in>| childrenSet tr \<Longrightarrow> (fset (\<Pi> child)) \<subseteq> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> ht UNIV))" using pathsForTreeLanguage_def \<Z>\<tau>_lemma mem_Collect_eq notin_fset subsetI  by (smt UNIV_I Z_def goodHeight_def heightOfChild less_imp_le_nat order_trans)
        
    have n65458 :  "\<Pi>\<^sub>\<iota>\<^sub>\<phi> forest = \<Pi> tr" using forest_def pathsSingeton by auto
        
    from n1   have n54687 : "symbol rule = root tr"  using rootRule by auto
        
    have "\<And> ht . ht > goodHeight \<Longrightarrow> fset (\<Pi> tr) \<subseteq> ((root tr) \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> ht UNIV) \<union> {[]}))" 
    proof 
      fix x
      assume a7678 : "x \<in> fset (\<delta>\<^sub>\<tau> tr)"
        
      obtain \<alpha> children where n54457 : "tr = NODE \<alpha> children"
        using tree.exhaust by auto 
      hence "x \<in> fset (fimage (\<lambda> tail.( \<alpha>#tail)) ((\<Union>| (fimage \<Pi> children)) |\<union>|  (finsert [] {||})))" using pathAlternateDef notin_fset  a7678 by auto
      hence n6587 : "x |\<in>| (fimage (\<lambda> tail.( \<alpha>#tail)) ((\<Union>| (fimage \<Pi> children)) |\<union>|  (finsert [] {||})))" using  notin_fset  by metis
      have n656898 : "childrenSet tr = children" using n54457 by auto
      have n656898b : "root tr = \<alpha>" using n54457 by auto
          
      show "\<And> ht . ht > goodHeight \<Longrightarrow>x \<in> ((root tr) \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> ht UNIV) \<union> {[]}))" 
      proof (rule disjE)
        from n6587 show "(x |\<in>| (fimage (\<lambda> tail.( \<alpha>#tail)) ((\<Union>| (fimage \<Pi> children))))) \<or> (x |\<in>| (fimage (\<lambda> tail.( \<alpha>#tail))  (finsert [] {||})))" by blast
        {
          assume "(x |\<in>| (fimage (\<lambda> tail.( \<alpha>#tail)) ((\<Union>| (fimage \<Pi> children)))))"
          then obtain child where "child |\<in>| children" and "x |\<in>| (fimage (\<lambda> tail.( \<alpha>#tail)) (\<Pi> child))" using n67789564 by auto
          then have n5458o98 : "x \<in> (image (\<lambda> tail.( \<alpha>#tail)) (fset (\<Pi> child)))" using notin_fset
            by force 
          from n6587 n656898 n5458o98 have "\<And> ht . ht > goodHeight \<Longrightarrow>x \<in> (image (\<lambda> tail.( \<alpha>#tail)) (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> ht UNIV)))"
            using \<open>child |\<in>| children\<close> n7588 by fastforce 
          then have "\<And> ht . ht > goodHeight \<Longrightarrow>x \<in> (image (\<lambda> tail.( (root tr)#tail)) (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> ht UNIV)))" using n656898b by auto
          then have "\<And> ht . ht > goodHeight \<Longrightarrow>x \<in> (image (\<lambda> tail.( (root tr)#tail)) (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> ht UNIV) \<union> {[]}))" by auto
          then show "\<And> ht . ht > goodHeight \<Longrightarrow>x \<in> ((root tr) \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> ht UNIV) \<union> {[]}))" using prefixLetter_def by auto
        }
        {
          assume "(x |\<in>| (fimage (\<lambda> tail.( \<alpha>#tail))  (finsert [] {||})))"
          then have "\<And> ht . ht > goodHeight \<Longrightarrow>x \<in> (image (\<lambda> tail.( (root tr)#tail)) (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> ht UNIV) \<union> {[]}))" using n656898b by auto
          then show "\<And> ht . ht > goodHeight \<Longrightarrow>x \<in> ((root tr) \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> ht UNIV) \<union> {[]}))" using prefixLetter_def by auto
        }
      qed
    qed
    then have "((\<And> ht.(ht > goodHeight \<Longrightarrow>  (forest \<in> \<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) rule \<and>  fset (\<Pi>\<^sub>\<iota>\<^sub>\<phi> forest) \<subseteq> root tr \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> ht UNIV) \<union> {[]})))))" using realizedInForest_def n65687 n65458  n54687 by auto
    then have "((\<And> ht.(ht > goodHeight \<Longrightarrow>  (realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) rule) ((root tr) \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> ht UNIV) \<union> {[]}))))))" using realizedInForest_def n65687 n65458  n54687 by blast
    then have "((\<And> ht.(ht > goodHeight \<Longrightarrow>  (realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) rule) ((symbol rule) \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> ht UNIV) \<union> {[]}))))))" using  n54687 by simp
    then show "(\<exists> goodHeight.(\<forall> ht.(ht > goodHeight \<longrightarrow>  (realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) rule) ((symbol rule) \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> ht UNIV) \<union> {[]}))))))" by auto
  qed
    
  from n6567987 have n6587 : "\<And>i. \<exists>goodHeight. (\<forall> ht . (ht>goodHeight \<longrightarrow>  (\<forall> rule. rule |\<in>| rule_set (\<A> i) \<longrightarrow> realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) rule) (symbol rule \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> ht UNIV) \<union> {[]})))))"  
  proof -
    fix i
    def P == "\<lambda> rule ht . (realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) rule) (symbol rule \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> ht UNIV) \<union> {[]})))"
    from commuteExistsAll2 have "\<And> (D :: (stt,abc) rule fset) (P :: (stt,abc) rule \<Rightarrow> nat \<Rightarrow> bool) . ((\<And>d. d |\<in>| D \<Longrightarrow> \<exists>n. \<forall>n2>n. P (d :: (stt,abc) rule) n2) \<Longrightarrow> \<exists>N. \<forall>d. d |\<in>| D \<longrightarrow> (\<forall>n2>N. P d n2))" by blast
        
    hence "\<And> (D :: (stt,abc) rule fset)  . ((\<And>d. d |\<in>| D \<Longrightarrow> \<exists>n. \<forall>n2>n. P (d :: (stt,abc) rule) n2) \<Longrightarrow> \<exists>N. \<forall>d. d |\<in>| D \<longrightarrow> (\<forall>n2>N. P d n2))" by auto
    hence ny687 : "((\<And>d. d |\<in>| (rule_set (\<A> i)) \<Longrightarrow> \<exists>n. \<forall>n2>n. P (d :: (stt,abc) rule) n2) \<Longrightarrow> \<exists>N. \<forall>d. d |\<in>| (rule_set (\<A> i)) \<longrightarrow> (\<forall>n2>N. P d n2))" by auto
    have "(\<And>d. d |\<in>| (rule_set (\<A> i)) \<Longrightarrow> \<exists>n. \<forall>n2>n. P (d :: (stt,abc) rule) n2)" using P_def n6567987
      by simp 
    hence "\<exists>N. \<forall>d. d |\<in>| (rule_set (\<A> i)) \<longrightarrow> (\<forall>n2>N. P d n2)" using ny687 by auto
    then show "\<exists>goodHeight. (\<forall> ht . (ht>goodHeight \<longrightarrow>  (\<forall> rule. rule |\<in>| rule_set (\<A> i) \<longrightarrow> realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) rule) (symbol rule \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> ht UNIV) \<union> {[]})))))"   using P_def by blast
  qed
    
  def Q == "\<lambda> i ht. (\<forall> rule. rule |\<in>| rule_set (\<A> i) \<longrightarrow> realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) rule) (symbol rule \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> ht UNIV) \<union> {[]})))"
    
  def D == " (finsert \<aa>\<^sub>1  (finsert \<aa>\<^sub>2 fempty))"
  have n767987 : "\<And>i .i |\<in>| D" using D_def \<A>.cases by blast 
      
      
  from commuteExistsAll2 have "\<And> (D :: ot fset) (P :: ot \<Rightarrow> nat \<Rightarrow> bool) . ((\<And>d. d |\<in>| D \<Longrightarrow> \<exists>n. \<forall>n2>n. P (d :: ot ) n2) \<Longrightarrow> \<exists>N. \<forall>d. d |\<in>| D \<longrightarrow> (\<forall>n2>N. P d n2))" by blast
      
  hence "\<And> (D :: ot fset)  . ((\<And>d. d |\<in>| D \<Longrightarrow> \<exists>n. \<forall>n2>n. Q (d :: ot ) n2) \<Longrightarrow> \<exists>N. \<forall>d. d |\<in>| D \<longrightarrow> (\<forall>n2>N. Q d n2))" by auto
  hence n76898 : "((\<And>d. d |\<in>| D \<Longrightarrow> \<exists>n. \<forall>n2>n. Q (d :: ot ) n2) \<Longrightarrow> \<exists>N. \<forall>d. d |\<in>| D \<longrightarrow> (\<forall>n2>N. Q d n2))" by auto
  have "(\<And>d. d |\<in>| D \<Longrightarrow> \<exists>n. \<forall>n2>n. Q (d :: ot ) n2)"  using Q_def n6587 by auto 
  hence "\<exists>N. \<forall>d. d |\<in>| D \<longrightarrow> (\<forall>n2>N. Q d n2)" using n76898 by auto
  hence "\<exists>N. \<forall>d. d |\<in>| D \<longrightarrow> (\<forall>n2>N. (\<forall> rule. rule |\<in>| rule_set (\<A> d) \<longrightarrow> realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> d) rule) (symbol rule \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> n2 UNIV) \<union> {[]}))))" using Q_def by auto
      
  hence "\<exists>N. \<forall>d.  (\<forall>n2>N. (\<forall> rule. rule |\<in>| rule_set (\<A> d) \<longrightarrow> realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> d) rule) (symbol rule \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> n2 UNIV) \<union> {[]}))))" using n767987 by auto
  then have "\<exists>goodHeight. (\<forall> i. (\<forall> ht . (ht>goodHeight \<longrightarrow>  (\<forall> rule. rule |\<in>| rule_set (\<A> i) \<longrightarrow> realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) rule) (symbol rule \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> ht UNIV) \<union> {[]}))))))"  using commuteExistsAll n6587 by auto 
  then have "\<exists>goodHeight. (\<forall> \<alpha> . (\<forall> i. (\<forall> ht . (ht>goodHeight \<longrightarrow>  (\<forall> rule. rule |\<in>| rule_set (\<A> i) \<longrightarrow> (\<alpha> = (symbol rule) \<longrightarrow> realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) rule) (symbol rule \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> ht UNIV) \<union> {[]}))))))))" by auto
  then show " \<exists>n. realizesUniv n" using realizesUniv_def by blast
qed
  
  
  
  
    
    
definition \<N> :: "nat" where
  "\<N> = (SOME N.(constantIsSuitableForAllStates N \<and> realizesUniv N \<and> 1 \<le> N))"
  
  
lemma stateSets : "(state_set (\<A> \<aa>\<^sub>1)) = (state_set (\<A> \<aa>\<^sub>2))"  by (simp add: state_set_def) 
    
    
lemma chainMax2 : 
  shows " \<And> (A :: 'a fset) (B :: 'b fset) (C :: 'c fset) (D :: 'd fset) (P :: 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> nat \<Rightarrow> bool). 
((\<And> a b c d . a |\<in>| A \<Longrightarrow> b|\<in>|B \<Longrightarrow> c |\<in>| C \<Longrightarrow> d |\<in>| D \<Longrightarrow> (\<exists> n. (\<forall> n2 . (n2 > n \<longrightarrow> P a b c d n2)))) 
  \<Longrightarrow> (\<exists> N. (\<forall> a b c d . a |\<in>| A \<longrightarrow> b|\<in>|B \<longrightarrow> c |\<in>| C \<longrightarrow> d |\<in>| D \<longrightarrow> ((\<forall> n2 . (n2 > N \<longrightarrow> P a b c d n2))))))"
  using CombinatoricsBackground.chainMaximum by blast
    
         
proposition existsUniformConstant :
  assumes rulesLangsNonempty : "\<And> \<R> i r . (r |\<in>| rule_set (\<A> i) \<Longrightarrow>  ((\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) r)  \<noteq> {}))"
  shows "constantIsSuitableForAllStates \<N>"
    and "realizesUniv \<N>"
    and "1 \<le> \<N>"
proof -
  have n655687 : "\<And>i . i = \<aa>\<^sub>1 \<or> i = \<aa>\<^sub>2"    using \<A>.cases by blast 
  then have n6568 : "\<And>i . i |\<in>| (finsert \<aa>\<^sub>1  (finsert \<aa>\<^sub>2 fempty))"    by auto
  def A == "((finsert \<aa>\<^sub>1  (finsert \<aa>\<^sub>2 fempty)) :: ot fset)"
  def B ==  "(state_set (\<A> \<aa>\<^sub>1)) |\<union>|(state_set (\<A> \<aa>\<^sub>2))"
  def C == "(fPow (state_set (\<A> \<aa>\<^sub>1)))"
  def D == "(fPow (state_set (\<A> \<aa>\<^sub>2)))"
  from chainMax2 have "\<And> (B :: stt fset) (C :: (stt fset) fset) (D :: (stt fset) fset) (P :: ot \<Rightarrow> stt \<Rightarrow> stt fset \<Rightarrow> stt fset \<Rightarrow> nat \<Rightarrow> bool). ((\<And> a b c d . a |\<in>| A \<Longrightarrow> b|\<in>|B \<Longrightarrow> c |\<in>| C \<Longrightarrow> d |\<in>| D \<Longrightarrow> (\<exists> n. (\<forall> n2 . (n2 > n \<longrightarrow> P a b c d n2)))) \<Longrightarrow> (\<exists> N. (\<forall> a b c d . a |\<in>| A \<longrightarrow> b|\<in>|B \<longrightarrow> c |\<in>| C \<longrightarrow> d |\<in>| D \<longrightarrow> ((\<forall> n2 . (n2 > N \<longrightarrow> P a b c d n2))))))" by blast
  then have " \<And> (P :: ot \<Rightarrow> stt \<Rightarrow> stt fset \<Rightarrow> stt fset \<Rightarrow> nat \<Rightarrow> bool). ((\<And> a b c d . a |\<in>| A \<Longrightarrow> b|\<in>|B \<Longrightarrow> c |\<in>| C \<Longrightarrow> d |\<in>| D \<Longrightarrow> (\<exists> n. (\<forall> n2 . (n2 > n \<longrightarrow> P a b c d n2)))) \<Longrightarrow> (\<exists> N. (\<forall> a b c d . a |\<in>| A \<longrightarrow> b|\<in>|B \<longrightarrow> c |\<in>| C \<longrightarrow> d |\<in>| D \<longrightarrow> ((\<forall> n2 . (n2 > N \<longrightarrow> P a b c d n2))))))" by blast
  then have n7667987 : " ((\<And> a b c d . a |\<in>| A \<Longrightarrow> b|\<in>|B \<Longrightarrow> c |\<in>| C \<Longrightarrow> d |\<in>| D \<Longrightarrow> (\<exists> n. (\<forall> n2 . (n2 > n \<longrightarrow> constantIsSuitableForStates a b c d n2)))) \<Longrightarrow> (\<exists> N. (\<forall> a b c d . a |\<in>| A \<longrightarrow> b|\<in>|B \<longrightarrow> c |\<in>| C \<longrightarrow> d |\<in>| D \<longrightarrow> ((\<forall> n2 . (n2 > N \<longrightarrow> constantIsSuitableForStates a b c d n2))))))" by blast
  from  constantLemma have "(\<And> i s Sa1 Sa2 . (s |\<in>| (state_set (\<A> i))  \<Longrightarrow>  ( Sa1 |\<subseteq>| state_set \<A>\<^sub>1   \<Longrightarrow> ( Sa2 |\<subseteq>| state_set \<A>\<^sub>2  \<Longrightarrow> (\<exists> N. constantIsSuitableForStates i s Sa1 Sa2 N )))))" by blast
  then have "(\<And> i s Sa1 Sa2 . (s |\<in>| (state_set (\<A> i)) \<Longrightarrow>  ( Sa1 |\<subseteq>| state_set \<A>\<^sub>1 \<Longrightarrow> ( Sa2 |\<subseteq>| state_set \<A>\<^sub>2  \<Longrightarrow> (\<exists> N. constantIsSuitableForStates i s Sa1 Sa2 N )))))" by blast
  then have "(\<And> i s Sa1 Sa2 . (s |\<in>| (state_set (\<A> i))\<Longrightarrow>  ( Sa1 |\<subseteq>| state_set \<A>\<^sub>1  \<Longrightarrow> ( Sa2 |\<subseteq>| state_set \<A>\<^sub>2 \<Longrightarrow>(\<exists> n. (\<forall> n2 . (n2 > n \<longrightarrow>  constantIsSuitableForStates i s Sa1 Sa2 n2 )))))))" using greaterConstantsAreGood  by metis
  hence "(\<And> i s Sa1 Sa2 . (s |\<in>| (state_set (\<A> i)) \<Longrightarrow>  ( Sa1 |\<in>| C \<Longrightarrow> ( Sa2 |\<in>| D  \<Longrightarrow>  (\<exists> n. (\<forall> n2 . (n2 > n \<longrightarrow> constantIsSuitableForStates i s Sa1 Sa2 n2 )))))))" using C_def D_def by auto
  then have "(\<And> a b c d . a |\<in>| A \<Longrightarrow> b|\<in>|B \<Longrightarrow> c |\<in>| C \<Longrightarrow> d |\<in>| D \<Longrightarrow> (\<exists> n. (\<forall> n2 . (n2 > n \<longrightarrow>constantIsSuitableForStates a b c d n2))))" using A_def B_def stateSets  n655687 by blast
  then have "(\<exists> N. (\<forall> a b c d . a |\<in>| A \<longrightarrow> b|\<in>|B \<longrightarrow> c |\<in>| C \<longrightarrow> d |\<in>| D \<longrightarrow> ((\<forall> n2 . (n2 > N \<longrightarrow> constantIsSuitableForStates a b c d n2)))))" using n7667987 by auto
  then have n767988 : "(\<exists> N. (\<forall> a b c d . a |\<in>| A \<longrightarrow> b|\<in>|B \<longrightarrow> c |\<subseteq>| state_set \<A>\<^sub>1  \<longrightarrow> d |\<subseteq>| state_set \<A>\<^sub>2  \<longrightarrow> ((\<forall> n2 . (n2 > N \<longrightarrow> constantIsSuitableForStates a b c d n2)))))" using C_def D_def by auto
  have "\<And> a b. ((a |\<in>| A \<and>  b|\<in>|B) = (a |\<in>| A \<and> b |\<in>| (state_set (\<A> a))))"  proof
    show "\<And>a b. a |\<in>| A \<and> b |\<in>| B \<Longrightarrow> a |\<in>| A \<and> b |\<in>| state_set (\<A> a)" using A_def B_def  using stateSets by blast 
    show "\<And>a b. a |\<in>| A \<and> b |\<in>| state_set (\<A> a) \<Longrightarrow> a |\<in>| A \<and> b |\<in>| B" using A_def B_def  using stateSets by blast 
  qed
  then have "(\<exists> N. (\<forall> a b c d . a |\<in>| A \<longrightarrow> b |\<in>| (state_set (\<A> a)) \<longrightarrow> c |\<subseteq>| state_set \<A>\<^sub>1  \<longrightarrow> d |\<subseteq>| state_set \<A>\<^sub>2  \<longrightarrow> ((\<forall> n2 . (n2 > N \<longrightarrow> constantIsSuitableForStates a b c d n2)))))" using n767988 by metis
  then have "(\<exists> N. (\<forall> a b c d . b |\<in>| (state_set (\<A> a)) \<longrightarrow> c |\<subseteq>| state_set \<A>\<^sub>1  \<longrightarrow> d |\<subseteq>| state_set \<A>\<^sub>2  \<longrightarrow> ((\<forall> n2 . (n2 > N \<longrightarrow> constantIsSuitableForStates a b c d n2)))))" using n655687 A_def    by simp 
  then have n6y5687 : "\<exists> N.  (\<forall> n2. n2 > N \<longrightarrow> constantIsSuitableForAllStates n2)" using constantIsSuitableForAllStates_def n6568  by (meson gt_ex)
  from assms realizedInUniv1 realizesUniv_def have "\<exists> n . \<forall> n2 . n2 > n \<longrightarrow> realizesUniv n2" by (meson less_trans)
      hence "\<exists> n . \<forall> n2 . n2 > n \<longrightarrow> (constantIsSuitableForAllStates n2 \<and> realizesUniv n2)" using n6y5687 less_add_Suc1 less_add_Suc2 less_trans
        by (metis add.left_commute add_lessD1) 
  then have  "\<exists> N. constantIsSuitableForAllStates N \<and> realizesUniv N \<and> 1 \<le> N" using n6y5687  less_add_Suc1 less_add_Suc2  by auto
  then have n5457 : "constantIsSuitableForAllStates \<N> \<and> realizesUniv \<N> \<and> 1 \<le> \<N>" using \<N>_def someI_ex    by (metis (mono_tags, lifting)) 
  then show "constantIsSuitableForAllStates \<N>"  by auto
  from n5457 show "realizesUniv \<N>" by auto
      from n5457 show "1 \<le> \<N>" by auto
qed
  
  
  
        
        
  
lemma realizedInUniv:
  fixes n r \<ii> 
  fixes \<alpha> :: abc
  assumes rulesLangsNonempty : "\<And> \<R> i r . (r |\<in>| rule_set (\<A> i) \<Longrightarrow>  ((\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) r)  \<noteq> {}))"
  assumes "\<N> < Suc n"
  assumes "r |\<in>| rule_set (\<A> \<ii>)"
  assumes "symbol r = \<alpha>"
  shows "realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>) r) (\<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> n UNIV) \<union> {[]}))"
proof -
  from existsUniformConstant assms(1) have "realizesUniv \<N>" by auto
  then have "(\<forall> i \<alpha> r n2. (Suc n2 > \<N> \<longrightarrow> (r |\<in>| rule_set (\<A> i) \<longrightarrow> symbol r = \<alpha> \<longrightarrow> (realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) r) (\<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> n2 UNIV) \<union> {[]}))))))" using realizesUniv_def by auto
  then show "(realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>) r) (\<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> n UNIV) \<union> {[]})))" using assms by auto
qed
  
  
  
  
  
definition \<V>\<^sub>\<tau> :: "ot \<Rightarrow> (stt,abc) rule \<Rightarrow> abc tree set" where
  "\<V>\<^sub>\<tau> ot r = {tr . (root tr = (symbol r)) \<and> \<Pi> tr \<in> ((upwardClosure (image \<Pi> (((Z \<N> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> ot) r)))))) 
                                 \<union> (image \<Pi> {t . height t > \<N>})) 
                              \<inter> (\<Inter>I \<in> (necess (\<A> ot) \<I> r) . (image \<Pi> (existential_satisfaction_set I)   ))}"
  
  (* ============================================= *)
section "Some Notions"   
  
fun numRange :: "nat \<Rightarrow> nat \<Rightarrow> nat set" where
  "numRange k l = {i . k \<le> i \<and> i \<le> l}"
  
fun prependWordToLanguage :: "'L list \<Rightarrow> 'L list fset set \<Rightarrow> 'L list fset set" where
  "prependWordToLanguage p l = image ((fimage (append p))) l"
  
fun prependWordToWordLanguage :: "'L list \<Rightarrow> 'L list set \<Rightarrow> 'L list set" where
  "prependWordToWordLanguage p l = image (((append p))) l"
  
  (* ============================================= *)
section "Basic Definitions For Lists"
  
  
fun pathFitsListAndListIsARun :: "ot \<Rightarrow>  abc node list \<Rightarrow> (stt,abc) rule list \<Rightarrow> bool" where
  "pathFitsListAndListIsARun \<ii> [] [] = True"
| "pathFitsListAndListIsARun \<ii> (a#b) (c#d) = (( (labelOfNode a = symbol c)
                                      \<and> (c |\<in>| rule_set (\<A> \<ii>))
                                      \<and> (( (down a)) \<in> ( \<V>\<^sub>\<tau> \<ii> c  )   )    )
                                      \<and> (pathFitsListAndListIsARun \<ii> b d)
                                      \<and> (\<forall> h.\<forall> t.(d = (h#t) \<longrightarrow>  (        (((transition (\<A> \<ii>) (states h) (symbol h) )  |\<in>| states c) )        )))        
                                      )"
| "pathFitsListAndListIsARun \<ii> (a#b) [] = False"
| "pathFitsListAndListIsARun \<ii> [] (a#b) = False"
  
  
  
  
  
lemma pathFitsListAndListIsARunImpliesV :
  fixes i
  fixes pi
  fixes run
  assumes "\<exists> a.\<exists>b.(pi = a#b)"
  assumes "(pathFitsListAndListIsARun i pi run)"
  shows "(( (down (hd pi))) \<in> ( \<V>\<^sub>\<tau> i (hd run)  )   ) "
  by (metis assms(1) assms(2) hd_Cons_tl list.sel(1) pathFitsListAndListIsARun.simps(2) pathFitsListAndListIsARun.simps(3))
    
    
lemma nonMatching :
  fixes i
  shows "\<And> e1 e2 . (pathFitsListAndListIsARun i (e1#e2) [] = False)"
  by simp
    
    
definition stateFromRule where "stateFromRule \<ii> r = (transition (\<A> \<ii>) (states (r)) (symbol (r)))"
  
  
definition pathSatisfiesApproximatorForRuleSet where
  "pathSatisfiesApproximatorForRuleSet p rules \<ii> = 
          (\<exists> r  . (hd r |\<in>| rules) \<and>
                      (pathFitsListAndListIsARun \<ii> p r))"
  
definition pathSatisfiesApproximatorForStateFromRuleSet where
  "pathSatisfiesApproximatorForStateFromRuleSet p rules \<ii> = 
          (\<exists> r  . \<exists>rule \<in> (fset rules) . ((stateFromRule  \<ii> (hd r)) |\<in>| (states rule)) \<and>
                      (pathFitsListAndListIsARun \<ii> p r))"
  
  
definition satisfiesApproximatorForStatesFromRuleSet where
  "satisfiesApproximatorForStatesFromRuleSet tr rules \<ii> = 
          (\<forall> p \<in> (pathsInTree tr) . 
             pathSatisfiesApproximatorForStateFromRuleSet p rules \<ii>)"
  
definition satisfiesApproximatorForRuleSet where
  "satisfiesApproximatorForRuleSet tr rules \<ii> = 
          (\<forall> p \<in> (pathsInTree tr) . 
             pathSatisfiesApproximatorForRuleSet p rules \<ii>)"
  
definition approximatorLanguageForRuleSet where
  "approximatorLanguageForRuleSet rules \<ii> = {tr .  satisfiesApproximatorForRuleSet tr rules \<ii>}"
  
  
  
  
  (* ============================================== *)
  
definition closedUnderPlus :: "'L tree fset set \<Rightarrow> bool" where
  "closedUnderPlus l = (\<forall> a \<in> l. (\<forall> b \<in> l. (plus a b \<in> l)))"
  
definition closedUnderArbitraryPlus :: "'L tree fset set \<Rightarrow> bool" where
  "closedUnderArbitraryPlus l = (\<forall> a . a \<noteq> fempty \<longrightarrow> (fset a) \<subseteq> l \<longrightarrow> (\<Union>| a) \<in> l)"
  
  
definition closedUnderPlusD :: "'L list fset set \<Rightarrow> bool" where
  "closedUnderPlusD l = (\<forall> a \<in> l. (\<forall> b \<in> l. (plusD a b \<in> l)))"
  
  
  
lemma pathInPlus :
  fixes f1 :: "abc tree fset"
  fixes f2 :: "abc tree fset"
  assumes b0 : "x |\<in>|\<Pi>\<^sub>\<iota>\<^sub>\<phi> f1"
  shows "x |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> (plus f1 f2)"
proof -
  from  plus_def fimage_mono sup_ge1 have b2 : "(\<Pi> |`| f1) |\<subseteq>| (\<Pi> |`| (plus f1 f2))" by  blast
  from ffUnionMono pathsInForest_def b2 pathsInForest_def b0 show ?thesis using fset_rev_mp by metis
qed
  
lemma plusComm :
  shows "plus f1 f2 = plus f2 f1"
  by (simp add: plus_def sup_commute)
    
lemma plusCommD :
  shows "plusD f1 f2 = plusD f2 f1"
  by (simp add: plusD_def sup_commute)
    
    
  
fun caseDistinction :: "bool \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "caseDistinction True x y = x"
| "caseDistinction False x y = y"
  
lemma caseDistinctionLemma :
  shows "(\<W> \<longrightarrow> (caseDistinction \<W> x y = x)) \<and> ((\<not> \<W>) \<longrightarrow> (caseDistinction \<W> x y = y))"
  by simp 
    
    
definition unrealizedRules :: "(ot \<Rightarrow> (stt,abc) rule fset) \<Rightarrow> (abc list set) \<Rightarrow> (ot \<times> (stt,abc) rule) set" where
  "unrealizedRules \<W> prevF = {(\<ii>,r) . r |\<in>| (\<W> \<ii>) \<and> (\<not> (realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>) r) ((symbol r)  \<bullet> (prevF \<union> {[]}))))}"
definition thereIsAnUnrealizedRule :: "(ot \<Rightarrow> (stt,abc) rule fset) \<Rightarrow> (abc list set) \<Rightarrow> bool" where
  "thereIsAnUnrealizedRule \<W> prevF = (unrealizedRules \<W> prevF \<noteq> {})"
definition chosenUnrealizedRule :: "(ot \<Rightarrow> (stt,abc) rule fset) \<Rightarrow> (abc list set) \<Rightarrow> (ot \<times> (stt,abc) rule)" where
  "chosenUnrealizedRule \<W> prevF = (SOME x. x \<in> (unrealizedRules \<W> prevF))"
definition chosenSide :: "(ot \<Rightarrow> (stt,abc) rule fset) \<Rightarrow> (abc list set) \<Rightarrow> ot" where
  "chosenSide \<W> prevF = \<pi>\<^sup>1 (chosenUnrealizedRule \<W> prevF)"
  
definition treesWithoutAnalysis :: "(ot \<Rightarrow> (stt,abc) rule fset) \<Rightarrow> (abc tree fset) \<Rightarrow> (ot \<times> abc tree) set" where
  "treesWithoutAnalysis \<W> \<ff> = {(i,p). p |\<in>| \<ff> \<and> \<not> (satisfiesApproximatorForStatesFromRuleSet  p (\<W> i) i  )  }"
definition thereIsTreeWithoutAnalysis :: "(ot \<Rightarrow> (stt,abc) rule fset) \<Rightarrow> (abc tree fset) \<Rightarrow> bool" where
  "thereIsTreeWithoutAnalysis \<W> \<ff> = (\<exists> x . x \<in> (treesWithoutAnalysis \<W> \<ff>))"
definition chosenTreeWithoutAnalysis :: "(ot \<Rightarrow> (stt,abc) rule fset) \<Rightarrow> (abc tree fset) \<Rightarrow> abc tree" where
  "chosenTreeWithoutAnalysis \<W> \<ff> = \<pi>\<^sup>2 (SOME x. x\<in> (treesWithoutAnalysis \<W> \<ff>))"
  
  
definition fInter :: "('a \<Rightarrow> 'b fset) \<Rightarrow> 'b fset" where
  "fInter u = Abs_fset (\<Inter> j. fset (u j))"
  
  
  
  
lemma pathsOfChildren :
  fixes pi tr \<alpha>
  assumes h1 : "pi |\<in>| \<Pi> tr"
  assumes "root tr = \<alpha>"
  assumes "pi = x#y#z"
  obtains tail child where "pi = \<alpha>#tail" and "child |\<in>| childrenSet tr" and "tail |\<in>| \<Pi> child"
proof -
  assume h0 : "(\<And> tail child. pi = \<alpha> # tail \<Longrightarrow> child |\<in>| childrenSet tr \<Longrightarrow> tail |\<in>| \<Pi> child \<Longrightarrow> thesis)"
  from h1 have h2 : "pi |\<in>| fimage (append [\<alpha>]) ((\<Union>| (fimage \<Pi> (childrenSet tr))) |\<union>|  (finsert [] {||}))" by (metis (full_types) assms(2) childrenSet.elims \<Pi>.simps root.simps)
  from h2 obtain tail where h3 : "tail |\<in>| (\<Union>| (fimage \<Pi> (childrenSet tr))) |\<union>|  (finsert [] {||})" and h4 : "pi = \<alpha>#tail" using append_Cons append_Nil fimageE    by force
  from h3 h4 assms(3) have h3b : "tail |\<in>| (\<Union>| (fimage \<Pi> (childrenSet tr)))"        by blast
  from h3b obtain child where h5 : "child |\<in>| childrenSet tr" and h6 : "tail |\<in>| \<Pi> child" by (metis (no_types, lifting) ffUnionLemma fimageE)
  from h0 h3 h4 h5 h6 show "thesis" by metis
qed
  
  
lemma pathsOfFactorDown :
  fixes p \<alpha> l tail
  assumes h1 : "p \<in> \<Pi>\<^sub>\<tau> l"
  assumes h2 : "p = \<alpha>#tail"
  assumes h10 : "tail = q#r"
  shows "tail \<in> \<Pi>\<^sub>\<tau> (\<alpha> \<diamondop>\<tau>\<lambda> l)"
proof -
  from h1 obtain tr where h3 : "p |\<in>| \<Pi> tr" and h7 : "tr \<in> l" using mem_Collect_eq pathsForTreeLanguage_def by auto
  from h3 h2 h10 have h4 : "root tr = \<alpha>" using list.inject pathsOfChildren by fastforce
  from h2 h3 h4 h10 pathsOfChildren obtain child where h5 : "child |\<in>| childrenSet tr" and h6 : "tail |\<in>| \<Pi> child" using list.inject by force
  from h7 h5 h4 h6 have h8 : "child \<in> (\<alpha> \<diamondop>\<tau>\<lambda> l)" using factorByRootSymbol_def mem_Collect_eq by auto
  from h6 h8 show "tail \<in> \<Pi>\<^sub>\<tau> (\<alpha> \<diamondop>\<tau>\<lambda> l)" using mem_Collect_eq pathsForTreeLanguage_def by auto
qed
  
  
  
  

  
lemma factorAndPrefix :
  fixes \<alpha>
  assumes b0 : "\<And> tr . tr \<in> l \<Longrightarrow> root tr = \<alpha>"
  assumes b20 : "witness \<in> l"
  shows "\<alpha> \<bullet> (\<Pi>\<^sub>\<tau> (\<alpha> \<diamondop>\<tau>\<lambda> l)) \<union> (insert [\<alpha>] {}) = \<Pi>\<^sub>\<tau> l"
proof
  from prefixLetter_def have "\<alpha> \<bullet> (\<Pi>\<^sub>\<tau> (\<alpha> \<diamondop>\<tau>\<lambda> l)) = (\<lambda>x.(\<alpha>#x)) ` (\<Pi>\<^sub>\<tau> (\<alpha> \<diamondop>\<tau>\<lambda> l))" by auto
  show "\<alpha> \<bullet> (\<Pi>\<^sub>\<tau> (\<alpha> \<diamondop>\<tau>\<lambda> l)) \<union> (insert [\<alpha>] {}) \<subseteq> \<Pi>\<^sub>\<tau> l"
  proof
    fix x
    assume b1 : "x \<in> \<alpha> \<bullet> (\<Pi>\<^sub>\<tau> (\<alpha> \<diamondop>\<tau>\<lambda> l))\<union> (insert [\<alpha>] {})"
    show "x \<in> \<Pi>\<^sub>\<tau> l"
    proof (rule disjE)
      from b1 show b1b : "x \<in> \<alpha> \<bullet> (\<Pi>\<^sub>\<tau> (\<alpha> \<diamondop>\<tau>\<lambda> l)) \<or> x \<in> (insert [\<alpha>] {})" by auto
      {
        assume b1c : "x \<in> \<alpha> \<bullet> (\<Pi>\<^sub>\<tau> (\<alpha> \<diamondop>\<tau>\<lambda> l))"
        from b1c prefixLetter_def obtain tail where b3 : "x = \<alpha>#tail" and b2 : "tail \<in> \<Pi>\<^sub>\<tau> (\<alpha> \<diamondop>\<tau>\<lambda> l)" by blast
        from b2 pathsForTreeLanguage_def obtain tree where b4 : "tree \<in> (\<alpha> \<diamondop>\<tau>\<lambda> l)" and b5 : "tail |\<in>| \<Pi> tree" by blast
        from b4 b4 factorByRootSymbol_def obtain tree0 where b6 : "tree0 \<in> l" and b7 : "root tree0 = \<alpha>" and b8 : "tree |\<in>| childrenSet tree0" by blast
        from paths_def b3 b5 b7 b8 root.simps  have b9 : "x |\<in>| \<Pi> tree0" by (metis childrenSet.elims)   
        from b9 b6 pathsForTreeLanguage_def show "x \<in> \<Pi>\<^sub>\<tau> l" by blast
      }
      from b0 have  "\<And> tr . (tr \<in> l \<Longrightarrow> ([\<alpha>] |\<in>| \<Pi> tr))" using rootIsPath    by (metis root.elims) 
      then have "[\<alpha>]\<in> \<Pi>\<^sub>\<tau> l" using pathsForTreeLanguage_def b20 by blast
      then  show "x \<in> (insert [\<alpha>] {}) \<Longrightarrow> x \<in> \<Pi>\<^sub>\<tau> l" by blast
    qed
      
  qed
  show "\<Pi>\<^sub>\<tau> l \<subseteq> \<alpha> \<bullet> (\<Pi>\<^sub>\<tau> (\<alpha> \<diamondop>\<tau>\<lambda> l)) \<union> (insert [\<alpha>] {})"
  proof
    fix x
    assume b1 : "x \<in> \<Pi>\<^sub>\<tau> l"
    from b1 pathsForTreeLanguage_def obtain tree where b2 : "x |\<in>| \<Pi> tree" and b3 : "tree \<in> l" by blast
    from b0 b3 have b4 : "root tree = \<alpha>" by auto
    from b4 b2 noEmptyPathsInPi b4 obtain tail where b5 : "x = \<alpha>#tail" by (metis pathsOfChildren)
    show "x \<in> \<alpha> \<bullet> (\<Pi>\<^sub>\<tau> (\<alpha> \<diamondop>\<tau>\<lambda> l))\<union> (insert [\<alpha>] {})"
    proof (rule disjE)
      show "tail = [] \<or> (\<exists> p . (\<exists> q. (tail=p#q)))" using list.exhaust by blast
          
          
      from b2 b5 have b6 : "(\<exists> p . (\<exists> q. (tail=p#q))) \<Longrightarrow> tail \<in> \<Pi>\<^sub>\<tau> (\<alpha> \<diamondop>\<tau>\<lambda> l)" using b1 pathsOfFactorDown by auto
      from prefixLetter_def b6 b5 show "(\<exists> p . (\<exists> q. (tail=p#q))) \<Longrightarrow> x \<in> \<alpha> \<bullet> (\<Pi>\<^sub>\<tau> (\<alpha> \<diamondop>\<tau>\<lambda> l)) \<union> (insert [\<alpha>] {})" by (simp add: rev_image_eqI) 
      from b5 show "tail = [] \<Longrightarrow> x \<in> \<alpha> \<bullet> (\<Pi>\<^sub>\<tau> (\<alpha> \<diamondop>\<tau>\<lambda> l)) \<union> (insert [\<alpha>] {})"          by simp
          
    qed
  qed
qed
  
  
definition \<P> where
  "\<P> rules = {tr . \<forall> \<ii>. satisfiesApproximatorForRuleSet tr (rules \<ii>) \<ii>}"
  
  
definition \<P>\<^sub>\<sigma> where
  "\<P>\<^sub>\<sigma> rules = {tr . \<forall> \<ii>. satisfiesApproximatorForStatesFromRuleSet tr (rules \<ii>) \<ii>}"
  
definition \<P>\<^sub>1 where
  "\<P>\<^sub>1 rules \<ii> = {tr . satisfiesApproximatorForRuleSet tr (rules \<ii>) \<ii>}"
  
  
  
lemma pathInChild:
  fixes pi :: "abc node list"
  assumes b1 : "p |\<in>| childrenSet p2"
  assumes b2 : "pi \<in> (pathsInTree p)"
  obtains piExt rootNode where "piExt = rootNode#pi" and "piExt \<in> (pathsInTree p2)"
proof 
  def rootNode == "SOME node . down (node :: abc node) = p2"
  from rootNode_def have a21 : "down rootNode = p2"      by (metis (mono_tags, lifting) node.select_convs(2) someI_ex)
  def piExt == "rootNode#pi"
  from b2 pathsInTree_def have "isAPathp pi"    by (simp add: pathsInTree_def)
  then obtain e1 tail where a20 : "pi = e1#tail" using isAPathp.simps        by blast
  have a10 : "(immediatelyDominates rootNode e1)"
  proof -
    from a20 b2 pathsInTree_def have "down e1 = p"      by (simp add: pathsInTree_def)
    then have "(   ((down e1) |\<in>| (childrenSet (down rootNode)))                                 )" using b1 a21 by auto
    then show "(immediatelyDominates rootNode e1)" using immediatelyDominates_def by auto
  qed
  have a25 : "(isAPathp piExt)" using a20    using \<open>isAPathp pi\<close> a10 isAPathp.intros(2) piExt_def by blast
  from piExt_def show "piExt = rootNode#pi" by auto
  from a25 a21 piExt_def show "piExt \<in> (pathsInTree p2)"      by (simp add: pathsInTree_def)
qed
  
  
  (* the following two are almost the same *)
lemma approximatorChildren :
  fixes p
  fixes p2
  fixes \<R>
  fixes i
  assumes b3 : "p |\<in>| childrenSet p2"
  assumes b4 : "(\<forall> pi \<in> (pathsInTree p2) . pathSatisfiesApproximatorForRuleSet pi  (\<R> i ) i)"
  shows "(\<forall> pi \<in> (pathsInTree p) . pathSatisfiesApproximatorForStateFromRuleSet pi  ((\<R> i )) i)"
proof 
  fix pi
  assume b0 : "pi \<in> (pathsInTree p)"
  from pathSatisfiesApproximatorForStateFromRuleSet_def have b14 : "pathSatisfiesApproximatorForStateFromRuleSet pi (\<R> i) i = 
          (\<exists> r  . \<exists>rule \<in> (fset (\<R> i)) . ((stateFromRule  i (hd r)) |\<in>| (states rule)) \<and>
                      (pathFitsListAndListIsARun i pi r))" by metis
  from b0 b3 pathInChild obtain piExt rootNode where b1 : "piExt = rootNode#pi" and b2 : "piExt \<in> (pathsInTree p2)" by blast
  from b4 b2 have b5 : "pathSatisfiesApproximatorForRuleSet piExt  (\<R> i ) i" by metis
  from b5 pathSatisfiesApproximatorForRuleSet_def obtain r where b6 : "hd r |\<in>| (\<R> i)" and b7 : "pathFitsListAndListIsARun i piExt r" by auto
  from b7 b1 obtain rTail where b8 : "r = (hd r)#rTail" and b9 : "pathFitsListAndListIsARun i (rootNode#pi) ((hd r)#rTail)" by (metis list.exhaust_sel nonMatching) 
  from b8 b9 have b10 : "(( (labelOfNode rootNode = symbol (hd r)) 
                                      \<and> (( (down rootNode)) \<in> ( \<V>\<^sub>\<tau> i (hd r)  )   )    )
                                      \<and> (pathFitsListAndListIsARun i pi rTail)
                                      \<and> (\<forall> h.\<forall> t.(rTail = (h#t) \<longrightarrow>  (        (((transition (\<A> i) (states h) (symbol h) )  |\<in>| states (hd r)) )        )))        
                                      )" using pathFitsListAndListIsARun.simps(2) by blast 
  from b10 have b11 : "(pathFitsListAndListIsARun i pi rTail)" by auto
  def rule == "hd r"
  from b6 rule_def have b12 : "rule \<in> (fset (\<R> i))" using notin_fset by force
  from b10 have b16 : "(pathFitsListAndListIsARun i pi rTail)" by auto
  from b10 have b17 : " (\<forall> h.\<forall> t.(rTail = (h#t) \<longrightarrow>  (        (((transition (\<A> i) (states h) (symbol h) )  |\<in>| states (hd r)) )        ))) " by auto
  from rule_def b10 have b18 : " (\<forall> h.\<forall> t.(rTail = (h#t) \<longrightarrow>  (        (((transition (\<A> i) (states h) (symbol h) )  |\<in>| states rule) )        ))) " by auto
  from noEmptyPaths pathsInTree_def b0 have b30 : "pi \<noteq> []" using list.distinct(1) mem_Collect_eq by auto 
  from b11 b30 have b21 : "rTail \<noteq> []" by (metis list.exhaust nonMatching)
  from b21 have b19 : "\<exists>t. rTail = ((hd rTail)#t)" by (metis list.collapse) 
  from b17 b18 b19 stateFromRule_def b18 b19 have b13 : "((stateFromRule  i (hd rTail)) |\<in>| (states rule))" by metis
  from b11 b12 b13 have b15 : "(\<exists>rule \<in> (fset (\<R> i)) . ((stateFromRule  i (hd rTail)) |\<in>| (states rule)) \<and>
                      (pathFitsListAndListIsARun i pi rTail))" by metis
  from b14 b15 show "pathSatisfiesApproximatorForStateFromRuleSet pi  (\<R> i ) i" by metis
qed
  
  
  
lemma approxForRuleAndChildrenStates :
  fixes tree
  fixes \<R>
  fixes x
  assumes "tree \<in> \<P> \<R>"
  assumes "x |\<in>| childrenSet tree"
  shows "x \<in> \<P>\<^sub>\<sigma> \<R>"
proof -
  from \<P>_def \<P>\<^sub>\<sigma>_def approximatorChildren show ?thesis by (smt assms(1) assms(2) mem_Collect_eq satisfiesApproximatorForRuleSet_def satisfiesApproximatorForStatesFromRuleSet_def)
qed
  
  
  
  
  
definition \<ff> where "\<ff> n \<R> = \<Z>\<^sub>\<tau> n (\<P> \<R>)"
  
definition \<gg> where "\<gg> n \<R> = \<Union>| (\<Z>\<^sub>\<phi> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (((\<R>) \<aa>\<^sub>1))((((\<R>) \<aa>\<^sub>2)))))"
  
fun \<W> :: "nat \<Rightarrow> nat \<Rightarrow> (ot \<Rightarrow> (stt,abc) rule fset) \<Rightarrow> ot \<Rightarrow> (stt,abc) rule fset"
  and \<ff>\<^sub>1 :: "nat \<Rightarrow> nat \<Rightarrow>  (ot \<Rightarrow> (stt,abc) rule fset) \<Rightarrow> abc tree fset"
  where 
    "\<W> n 0 \<R> i = \<R> i"
  | "\<ff>\<^sub>1 n 0 \<R> = \<Z>\<^sub>\<tau> n UNIV"
  | "\<W>  n (Suc k) \<R> i = caseDistinction (((thereIsAnUnrealizedRule  (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))) 
                                           \<and>  (i = chosenSide  (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))))))
                                           ((\<W> n k \<R> i) |-| {|\<pi>\<^sup>2 (chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))))|})
                                           (\<W> n k \<R> i)"
  | "\<ff>\<^sub>1 n (Suc k) \<R> = inf_fset2 (\<ff>\<^sub>1 n k \<R>)  (\<P>\<^sub>\<sigma> (\<W> n (k) \<R>))"
    
    
    
    
lemma fa_def2 : "\<And> n . \<ff>\<^sub>1 n (Suc k) \<R> = inf_fset2 (\<ff>\<^sub>1 n k \<R>)  (\<P>\<^sub>\<sigma> (\<W> n (k) \<R>))" by auto
    
    
    
lemma wStationaryLemma : 
  fixes l
  shows "(\<W> n l \<R>) = (\<W> n (Suc l) \<R>) \<Longrightarrow> \<not> (thereIsAnUnrealizedRule  (\<W> n l \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n l \<R>))))"
proof 
  assume y65 : "\<W> n l \<R> = \<W> n (Suc l) \<R>"
  assume y66 : "thereIsAnUnrealizedRule (\<W> n l \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n l \<R>))"
  def i == "chosenSide  (\<W> n l \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n l \<R>)))"
  from i_def y66 have y67 : "\<W> n (Suc l) \<R> i = ((\<W> n l \<R> i) |-| {|\<pi>\<^sup>2 (chosenUnrealizedRule (\<W> n l \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n l \<R>))))|})" by (simp add: \<W>.simps(2) caseDistinction.elims)
  from y66 i_def chosenUnrealizedRule_def thereIsAnUnrealizedRule_def have y68 : "\<pi>\<^sup>2 (chosenUnrealizedRule (\<W> n l \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n l \<R>)))) |\<in>| \<W> n (Suc l) \<R> i"
  proof -
    from thereIsAnUnrealizedRule_def y66 have n65 :  "(unrealizedRules (\<W> n l \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n l \<R>)) \<noteq> {})" by auto
    from chosenUnrealizedRule_def n65 have n66 : "chosenUnrealizedRule (\<W> n l \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n l \<R>))) \<in> (unrealizedRules (\<W> n l \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n l \<R>)))" by (metis all_not_in_conv someI_ex)
    from i_def chosenSide_def have n67 : "\<pi>\<^sup>1 (chosenUnrealizedRule (\<W> n l \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n l \<R>)))) = i" by simp
    from n66 n67 show "\<pi>\<^sup>2 (chosenUnrealizedRule (\<W> n l \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n l \<R>)))) |\<in>| \<W> n (Suc l) \<R> i" by (metis (no_types, lifting) case_prodE mem_Collect_eq prod.sel(1) prod.sel(2) unrealizedRules_def y65) 
  qed
  from y67 y68 have "\<W> n l \<R> \<noteq> \<W> n (Suc l) \<R>" by blast
  then show "False" using y65 by auto
qed
  
  
  
  
  
lemma factoredFInFa0 :
  fixes n
  fixes \<A>
  fixes \<R>
  assumes "\<And> i r . r |\<in>| \<R> i \<Longrightarrow> symbol r = \<alpha>"
  shows "(\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) |\<subseteq>| \<ff>\<^sub>1 n 0 \<R>"
proof
  have "\<ff>\<^sub>1 n 0 \<R> = \<Z>\<^sub>\<tau> n UNIV" by (simp)
  have b2 : "\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>) = set_to_fset {t. (\<exists>tree. tree |\<in>| ((\<ff> (Suc n)  \<R>)) \<and> (root tree = \<alpha> \<and> t |\<in>| childrenSet tree))}" by (simp add: factorByRootSymbolF_def)
  from b2 have b3 : "\<alpha> \<diamondop>\<tau>\<lambda> (fset (\<ff> (Suc n)  \<R>)) = {t. (\<exists>tree. tree \<in> (fset (\<ff> (Suc n)  \<R>)) \<and> (root tree = \<alpha> \<and> t |\<in>| childrenSet tree))}"
    using factorByRootSymbol_def by auto
  fix x
  assume b1 : "x |\<in>| \<alpha> \<diamondop> (\<ff> (Suc n) \<R>)"
  from factorByRootSymbolF_lemma b1 have b4 : "x \<in> \<alpha> \<diamondop>\<tau>\<lambda> (fset (\<ff> (Suc n)  \<R>))" by metis
  from b4 b3 have b5 : "(\<exists>tree. tree \<in> (fset (\<ff> (Suc n) \<R>)) \<and> (root tree = \<alpha> \<and> x |\<in>| childrenSet tree))" by blast
  from \<ff>_def have b6 : "(\<ff> (Suc n)  \<R>) = \<Z>\<^sub>\<tau> (Suc n) (\<P> \<R>)" by metis
  from b5 obtain tree where b8 : " tree \<in> (fset (\<ff> (Suc n) \<R>))" and b7 : "(root tree = \<alpha> \<and> x |\<in>| childrenSet tree)" by blast
  from b6 b8 have b9 : "tree \<in> (fset (\<Z>\<^sub>\<tau> (Suc n) (\<P> \<R>)))" by metis
  from b9 \<Z>\<^sub>\<tau>_def Z_def \<Z>\<tau>_lemma mem_Collect_eq have b10 : "tree \<in> (\<P> \<R>)" by blast
  from b9 Z_def \<Z>\<tau>_lemma mem_Collect_eq have b11 : "height tree \<le> (Suc n)" by metis
  from b11 heightOfChild  have b18 : "height x \<le> n" using b7 less_trans_Suc not_less by fastforce 
  from b7 have "x |\<in>| childrenSet tree" by metis
  from approxForRuleAndChildrenStates b10 b7 have b15 : "x \<in> (\<P>\<^sub>\<sigma> (\<R>))" by metis
  show "x |\<in>| \<ff>\<^sub>1 n 0 \<R>"
  proof -
    have "x \<in> Z n UNIV" using  Z_def b18 by blast
    then have "x |\<in>| \<Z>\<^sub>\<tau> n UNIV" using \<Z>\<tau>_lemma notin_fset by metis
    then show "x |\<in>| \<ff>\<^sub>1 n 0 \<R>" by simp 
  qed
qed
  
  
  
  
  
lemma zIntersectLemmaNofin :
  fixes l
  fixes n
  fixes x
  shows "(x \<in> Z n l) = ((x \<in> Z n UNIV) \<and> (x \<in> l))"
  using Z_def by auto
    
    
lemma zIntersectLemma :
  fixes l
  fixes n
  fixes x
  shows "(x |\<in>| \<Z>\<^sub>\<tau> n l) = ((x |\<in>| \<Z>\<^sub>\<tau> n UNIV) \<and> (x \<in> l))"
  using zIntersectLemmaNofin \<Z>\<tau>_lemma
  by (metis fmember.rep_eq) 
    
    
lemma zIntersectLemmaFin :
  fixes l
  fixes n
  fixes x
  shows "\<Z>\<^sub>\<tau> n l = inf_fset2 (\<Z>\<^sub>\<tau> n UNIV) l"
  using zIntersectLemma
  by (smt Int_iff fset_eqI inf_fset2.rep_eq notin_fset) 
    
lemma everythingAnalyzedImpliesSatisfiesImplications :
  fixes \<W>
  fixes \<ff>
  assumes b1 : "(\<not> (thereIsTreeWithoutAnalysis \<W> \<ff>))"
  assumes b5 : "\<ff> |\<subseteq>| \<Z>\<^sub>\<tau> n (UNIV)"
  shows "\<ff> |\<subseteq>| (((\<Z>\<^sub>\<tau> n (\<P>\<^sub>\<sigma>  \<W>))))"
proof 
  fix x
  assume b0 : "x |\<in>| \<ff>"
  from thereIsTreeWithoutAnalysis_def b1 treesWithoutAnalysis_def have b2 : "\<And> i p . p |\<in>| \<ff> \<Longrightarrow> (satisfiesApproximatorForStatesFromRuleSet p (\<W> i) i)" by (simp add: mem_Collect_eq prod.simps(2))
  from b0 b2 have b4 : "x \<in> (\<P>\<^sub>\<sigma> \<W>)" by (simp add: \<P>\<^sub>\<sigma>_def mem_Collect_eq)
  from b0 b5 b4 zIntersectLemma show "x |\<in>| (((\<Z>\<^sub>\<tau> n (\<P>\<^sub>\<sigma> \<W>))))" using fset_rev_mp by blast 
qed
  
  
  
  
  
lemma realized_rule_state_reverse : 
  fixes r
  fixes \<ii>
  assumes b0 : "symbol r = \<alpha>"
  assumes b1 : "\<And> state . (state |\<in>| (states r) \<Longrightarrow>  realizedIn (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> \<ii>) state) pathset)"
  shows "(realizedIn  (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) r) (\<alpha> \<bullet>  (pathset \<union> (insert [] {}))))"
proof -
  from b1 realizedIn_def have b2 : "\<And> state . (state |\<in>| (states r) \<Longrightarrow>   (\<exists>\<gg> . ((\<gg> \<in> (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> \<ii>) state)) \<and> (fset (\<Pi> \<gg>) \<subseteq> pathset))))" by metis
  def realizor == "\<lambda> state.(SOME g. ((g \<in> (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> \<ii>) state)) \<and> (fset (\<Pi> g) \<subseteq> pathset)))"
  from b2 realizor_def have b3 : "\<And> state . (state |\<in>| (states r) \<Longrightarrow>   ( (((realizor state) \<in> (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> \<ii>) state)) \<and> (fset (\<Pi> (realizor state)) \<subseteq> pathset))))"
    by (metis (no_types, lifting) someI_ex) 
  def children == "realizor |`| (states r)"
  def exampleTree == "(NODE \<alpha> children)"
  have b4 : "exampleTree \<in> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) r)"
  proof -
    from realizor_def b2 have realizorLemma : "\<And> state0 . state0 |\<in>| (states r) \<Longrightarrow> evaluation (\<A> \<ii>) (realizor state0) = state0" using b3 language_for_state_def by fastforce 
    from tree_for_rule_def language_for_rule_def 
    have c2 : "\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) r = {tree . ((root tree = symbol r) \<and> ((fimage (((evaluation (\<A> \<ii>)))) (childrenSet tree)) = states r))}" by (smt Collect_cong)
    from b0 exampleTree_def have "(root exampleTree = symbol r)" by (simp add: root.simps) 
    have g1 : "(fimage (((evaluation (\<A> \<ii>)))) (childrenSet exampleTree)) = states r"
    proof -
      from children_def exampleTree_def have f1 : "(realizor |`| (states r)) =  (childrenSet exampleTree)" by (simp add: childrenSet.simps)
      have f2 : "fimage (((evaluation (\<A> \<ii>)))) (realizor |`| (states r)) = states r"
      proof
        show "evaluation (\<A> \<ii>) |`| realizor |`| states r |\<subseteq>| states r"
        proof
          fix x
          assume d1 : "x |\<in>| evaluation (\<A> \<ii>) |`| (realizor |`| states r)"
          from d1 obtain y state0 where d2 : "y |\<in>| (realizor |`| states r)" and d3 : "x = evaluation (\<A> \<ii>) y" and d4 : "y = realizor state0" and d5 : "state0 |\<in>| states r"  using fimageE by blast
          from d5 realizorLemma d3 d4 d5 show "x |\<in>| states r" by metis
        qed
        show "states r |\<subseteq>| evaluation (\<A> \<ii>) |`| realizor |`| states r"
        proof
          fix x
          assume e1 : "x |\<in>| states r"
          from e1 realizorLemma show "x |\<in>| evaluation (\<A> \<ii>) |`| realizor |`| states r" by (metis fimageI)
        qed
      qed
      from f1 f2 show ?thesis by metis
    qed
    from c2 b0 g1 show ?thesis using \<open>root exampleTree = symbol r\<close> mem_Collect_eq by auto 
  qed
  have b5 : "fset (\<Pi> exampleTree) \<subseteq> (\<alpha> \<bullet>  (pathset \<union> (insert [] {})))"
  proof
    fix x
    assume g1 : "x \<in> fset (\<Pi> exampleTree)"
    from b2 realizor_def have y2 : "\<And> child. child |\<in>| children \<Longrightarrow> (fset (\<Pi> child) \<subseteq> pathset)" using b3 children_def by blast
    have y1 : "\<Pi> exampleTree = fimage (\<lambda> tail.(\<alpha>#tail)) ((\<Union>| (fimage \<Pi> children)) |\<union>|  (finsert [] {||})) " using  exampleTree_def pathAlternateDef by metis
    from g1 have g2 : "x |\<in>| (\<Pi> exampleTree)" by (meson notin_fset)
    from y1 g2 have g3 : "x |\<in>| fimage (\<lambda> tail.(\<alpha>#tail)) ((\<Union>| (fimage \<Pi> children)) |\<union>|  (finsert [] {||}))" by simp
    from g3 obtain y where g4 : "x = \<alpha>#y" and g5 : "y |\<in>| ((\<Union>| (fimage \<Pi> children)) |\<union>|  (finsert [] {||}))" by blast
    from g4 append_def have g6 : "x = \<alpha>#y" using Cons_eq_appendI self_append_conv2 by auto
    show "x \<in> (\<alpha> \<bullet>  (pathset \<union> (insert [] {})))" 
    proof (rule disjE)
      show "y = [] \<or> (\<exists> p .(\<exists>q.(y = p#q)))" using list.exhaust by auto
      from g6  show "y = [] \<Longrightarrow>   x \<in> (\<alpha> \<bullet>  (pathset \<union> (insert [] {})))"        by (simp add: prefixLetter_def)
      from g5 obtain child where g7 : "(\<exists> p .(\<exists>q.(y = p#q))) \<Longrightarrow> child |\<in>| children" and g8 : "(\<exists> p .(\<exists>q.(y = p#q))) \<Longrightarrow> y |\<in>| \<Pi> child" by (metis childrenSet.simps exampleTree_def g2 g6 list.sel(3) pathsOfChildren)
      from g8 y2 have g9 : "(\<exists> p .(\<exists>q.(y = p#q))) \<Longrightarrow> y \<in> pathset" using g7 notin_fset subsetCE      by fastforce
      from g6 g9 prefixLetter_def show "(\<exists> p .(\<exists>q.(y = p#q))) \<Longrightarrow> x \<in> (\<alpha> \<bullet>  (pathset \<union> (insert [] {})))" by (simp add: imageI)  
    qed
  qed
  from realizedIn_def b4 b5 show ?thesis by metis
qed
  
  
    
    
lemma \<Z>\<^sub>\<phi>\<^sub>F_mono : 
  assumes "L1 \<subseteq> L2"
  shows "\<Z>\<^sub>\<phi>\<^sub>F n L1 \<subseteq> \<Z>\<^sub>\<phi>\<^sub>F n L2"
  by (smt Int_iff \<Z>\<^sub>\<phi>\<^sub>F_def assms inf.absorb_iff2 subsetI)
    
    
lemma \<Z>\<^sub>\<phi>_mono : 
  assumes "L1 \<subseteq> L2"
  shows "\<Z>\<^sub>\<phi> n L1 |\<subseteq>| \<Z>\<^sub>\<phi> n L2"
  by (metis \<Z>\<^sub>\<phi>\<Z>\<^sub>\<phi>\<^sub>Flemma \<Z>\<^sub>\<phi>\<^sub>F_mono assms less_eq_fset.rep_eq)
    
    
lemma z_mono : 
  assumes "L1 \<subseteq> L2"
  shows "Z n L1 \<subseteq> Z n L2"
  by (metis (no_types, lifting) Collect_mono Z_def assms subsetCE)
    
    
lemma paths_monoForest : 
  assumes "L1 \<subseteq> L2"
  shows "\<Pi>\<^sub>\<phi> L1 \<subseteq> \<Pi>\<^sub>\<phi> L2"
  by (simp add: assms pathsForestLangMonotone)
    
lemma paths_monoTree : 
  assumes "L1 \<subseteq> L2"
  shows "\<Pi>\<^sub>\<tau> L1 \<subseteq> \<Pi>\<^sub>\<tau> L2"
  by (simp add: assms pathsTreeLangMonotone)
    
    
lemma wInR : shows "\<W> n k \<R> i |\<subseteq>| \<R> i" proof (induct k)
  case 0
  then show ?case
    by simp 
next
  case (Suc k)
  from \<W>.simps obtain cond diff where a1 : "\<W> n (Suc k) \<R> i = caseDistinction cond                                           ((\<W> n k \<R> i) |-| diff)                                           (\<W> n k \<R> i)" by auto
  have "cond = True \<Longrightarrow> \<W> n (Suc k) \<R> i = ((\<W> n k \<R> i) |-| diff)" using a1 caseDistinction.simps by simp
  then have a10 : "cond = True \<Longrightarrow> \<W> n (Suc k) \<R> i |\<subseteq>| ((\<W> n k \<R> i))" by blast 
  have a11 : "cond = False \<Longrightarrow> \<W> n (Suc k) \<R> i = ((\<W> n k \<R> i))" using a1 caseDistinction.simps by simp
  from a10 a11 show "\<W> n k \<R> i |\<subseteq>| \<R> i \<Longrightarrow> \<W> n (Suc k) \<R> i |\<subseteq>| \<R> i" by blast
qed
  
  
lemma w_mono :
  shows "(\<W> n k \<R>) \<ii> |\<subseteq>| \<R> \<ii>"
  by (simp add: wInR)
    
    
    
    (* ======================================= *)
    
lemma biguplusMono :
  fixes X Y
  assumes "X |\<subseteq>| Y"
  shows "(\<Uplus> X) \<subseteq> (\<Uplus> Y)"
  by (smt assms biguplusForests_def fset_rev_mp mem_Collect_eq subsetI)
    
    
lemma biguplusMonoD :
  fixes X Y
  assumes "X |\<subseteq>| Y"
  shows "(\<Uplus>\<^sub>\<delta> X) \<subseteq> (\<Uplus>\<^sub>\<delta> Y)"
  by (smt assms biguplusForestsD_def fset_rev_mp mem_Collect_eq subsetI)
    
    
lemma intersectMonoD :
  fixes R1 R2 S1 S2
  assumes \<aa>\<^sub>1 : "R1 |\<subseteq>| R2"
  assumes \<aa>\<^sub>2 : "S1 |\<subseteq>| S2"
  shows "\<Psi>\<^sub>\<Sigma>\<^sub>\<rho>\<^sub>\<delta> R1 S1 \<subseteq> \<Psi>\<^sub>\<Sigma>\<^sub>\<rho>\<^sub>\<delta> R2 S2"
proof -
  from \<Psi>\<^sub>\<Sigma>\<^sub>\<rho>\<^sub>\<delta>_def have a3 : "\<Psi>\<^sub>\<Sigma>\<^sub>\<rho>\<^sub>\<delta> R1 S1 = ( (((\<Uplus>\<^sub>\<delta> (((\<delta>\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| R1)))) 
                                              \<inter> ((\<Uplus>\<^sub>\<delta> (((\<delta>\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>2) |`| S1))))))" by metis 
  from \<Psi>\<^sub>\<Sigma>\<^sub>\<rho>\<^sub>\<delta>_def have a4 : "\<Psi>\<^sub>\<Sigma>\<^sub>\<rho>\<^sub>\<delta> R2 S2 = ( (((\<Uplus>\<^sub>\<delta> (((\<delta>\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| R2)))) 
                                              \<inter> ((\<Uplus>\<^sub>\<delta> (((\<delta>\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>2) |`| S2))))))" by simp
  from \<aa>\<^sub>1 have a5 : "((\<delta>\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| R1) |\<subseteq>| ((\<delta>\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| R2)" by blast
  from \<aa>\<^sub>2 have a6 : "((\<delta>\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| S1) |\<subseteq>| ((\<delta>\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| S2)" by blast
  from biguplusMonoD a5 have a7 : "(\<Uplus>\<^sub>\<delta> (((\<delta>\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| R1))) \<subseteq> (\<Uplus>\<^sub>\<delta> (((\<delta>\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| R2)))" by auto
  from biguplusMonoD a6 have a8 : "(\<Uplus>\<^sub>\<delta> (((\<delta>\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| S1))) \<subseteq> (\<Uplus>\<^sub>\<delta> (((\<delta>\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| S2)))" by auto
  from a7 have a9 : " ( (((\<Uplus>\<^sub>\<delta> (((\<delta>\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| R1)))) \<subseteq> ((\<Uplus>\<^sub>\<delta> (((\<delta>\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| R2)))) ))" by blast
  from a8 have a10 : " ( (((\<Uplus>\<^sub>\<delta> (((\<delta>\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| S1)))) \<subseteq> ((\<Uplus>\<^sub>\<delta> (((\<delta>\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| S2)))) ))" by blast
  from a9 a10 a3 a4 show "\<Psi>\<^sub>\<Sigma>\<^sub>\<rho>\<^sub>\<delta> R1 S1 \<subseteq> \<Psi>\<^sub>\<Sigma>\<^sub>\<rho>\<^sub>\<delta> R2 S2"  by (smt \<aa>\<^sub>2 biguplusMonoD fimage_finter_fsubset image_mono inf.boundedE inf.orderE inf_mono)
qed
  
lemma intersectMono :
  fixes R1 R2 S1 S2
  assumes \<aa>\<^sub>1 : "R1 |\<subseteq>| R2"
  assumes \<aa>\<^sub>2 : "S1 |\<subseteq>| S2"
  shows "\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> R1 S1 \<subseteq> \<Psi>\<^sub>\<Sigma>\<^sub>\<rho> R2 S2"
proof -
  from \<Psi>\<^sub>\<Sigma>\<^sub>\<rho>_def have a3 : "\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> R1 S1 = ( ((\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| R1)))) 
                                              \<inter> (\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>2) |`| S1))))))" by metis 
  from \<Psi>\<^sub>\<Sigma>\<^sub>\<rho>_def have a4 : "\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> R2 S2 = ( ((\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| R2)))) 
                                              \<inter> (\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>2) |`| S2))))))" by simp
  from \<aa>\<^sub>1 have a5 : "((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| R1) |\<subseteq>| ((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| R2)" by blast
  from \<aa>\<^sub>2 have a6 : "((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| S1) |\<subseteq>| ((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| S2)" by blast
  from biguplusMono a5 have a7 : "(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| R1))) \<subseteq> (\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| R2)))" by auto
  from biguplusMono a6 have a8 : "(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| S1))) \<subseteq> (\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| S2)))" by auto
  from a7 have a9 : " ( ((\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| R1)))) \<subseteq> (\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| R2)))) ))" by blast
  from a8 have a10 : " ( ((\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| S1)))) \<subseteq> (\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| S2)))) ))" by blast
  from a9 a10 a3 a4 show "\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> R1 S1 \<subseteq> \<Psi>\<^sub>\<Sigma>\<^sub>\<rho> R2 S2"  by (smt \<aa>\<^sub>2 biguplusMono fimage_finter_fsubset image_mono inf.boundedE inf.orderE inf_mono)
qed
  
  (* ======================================= *)
  
lemma ruleWentMissing :
  fixes r
  fixes \<R>
  fixes n
  fixes k
  fixes \<ii>
  assumes "r |\<in>| \<R> \<ii>"
  shows
    "(\<not>(r |\<in>|  ((\<W> n k \<R>) \<ii>))) \<Longrightarrow> (\<exists> k0. (k0 < k 
    \<and> r |\<in>| ((\<W> n k0 \<R>) \<ii>) 
    \<and> \<not> (r |\<in>| ((\<W> n (Suc k0) \<R>) \<ii>)) 
    \<and> chosenUnrealizedRule (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k0 \<R>))) = (\<ii>,r) 
    \<and> ((\<ii>,r) \<in> (unrealizedRules (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k0 \<R>))))))
    \<and> (\<ii>,r) \<in> (unrealizedRules (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k0 \<R>)))))"
proof (induct k)
  case 0
  assume "r |\<notin>| \<W> n 0 \<R> \<ii>"
  then have "False" using assms \<W>.simps by simp
  then show ?case by auto
next
  case (Suc k)
  assume b59 : "r |\<notin>| \<W> n (Suc k) \<R> \<ii>"
  have "r |\<notin>| \<W> n k \<R> \<ii> \<Longrightarrow>
    \<exists>k0. (k0 < k \<and> r |\<in>| \<W> n k0 \<R> \<ii> \<and> r |\<notin>| \<W> n (Suc k0) \<R> \<ii> \<and> chosenUnrealizedRule (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k0 \<R>)) = (\<ii>, r) \<and> (\<ii>, r) \<in> unrealizedRules (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k0 \<R>))) \<and>
         (\<ii>, r) \<in> unrealizedRules (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k0 \<R>))"      using Suc.hyps by auto
  show ?case
  proof (rule disjE)
    show "(True = (((thereIsAnUnrealizedRule  (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))))) \<and>  (\<ii> = chosenSide  (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))))) \<or> (False = ((((thereIsAnUnrealizedRule  (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))))) \<and>  (\<ii> = chosenSide  (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))))))" by auto
    {
      assume "False = (((thereIsAnUnrealizedRule  (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))))) \<and>  (\<ii> = chosenSide  (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))))" 
      hence w1 : "(False = (((thereIsAnUnrealizedRule  (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))))))) \<or> (False = (\<ii> = chosenSide  (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))))" by auto
      assume b60 : "False = (((thereIsAnUnrealizedRule  (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))))) \<and>  (\<ii> = chosenSide  (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))))"
      have "\<W>  n (Suc k) \<R> \<ii> = caseDistinction (((thereIsAnUnrealizedRule  (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))) 
                                           \<and>  (\<ii> = chosenSide  (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))))))
                                           ((\<W> n k \<R> \<ii>) |-| {|\<pi>\<^sup>2 (chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))))|})
                                           (\<W> n k \<R> \<ii>)" using \<W>.simps(2) by auto
      then have "\<W>  n (Suc k) \<R> \<ii> = caseDistinction False ((\<W> n k \<R> \<ii>) |-| {|\<pi>\<^sup>2 (chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))))|})  (\<W> n k \<R> \<ii>)" using b60 by auto
      then have "\<W>  n (Suc k) \<R> \<ii> = (\<W> n k \<R> \<ii>)" using caseDistinction.simps(2) by auto
      then have "r |\<notin>| \<W> n k \<R> \<ii>" using b59        using b60 by auto 
      hence "    \<exists>k0. (k0 < k \<and> r |\<in>| \<W> n k0 \<R> \<ii> \<and> r |\<notin>| \<W> n (Suc k0) \<R> \<ii> \<and> chosenUnrealizedRule (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k0 \<R>)) = (\<ii>, r) \<and> (\<ii>, r) \<in> unrealizedRules (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k0 \<R>))) \<and>
         (\<ii>, r) \<in> unrealizedRules (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k0 \<R>))"      using Suc.hyps by auto
      then show "    \<exists>k0. (k0 < (Suc k) \<and> r |\<in>| \<W> n k0 \<R> \<ii> \<and> r |\<notin>| \<W> n (Suc k0) \<R> \<ii> \<and> chosenUnrealizedRule (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k0 \<R>)) = (\<ii>, r) \<and> (\<ii>, r) \<in> unrealizedRules (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k0 \<R>))) \<and>
         (\<ii>, r) \<in> unrealizedRules (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k0 \<R>))"            using less_SucI by blast
    }
    {
      assume b70 : "True = (((thereIsAnUnrealizedRule  (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))))) \<and>  (\<ii> = chosenSide  (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))))"
      have "\<W>  n (Suc k) \<R> \<ii> = caseDistinction (((thereIsAnUnrealizedRule  (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))) \<and>  (\<ii> = chosenSide  (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))))))
                                           ((\<W> n k \<R> \<ii>) |-| {|\<pi>\<^sup>2 (chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))))|})
                                           (\<W> n k \<R> \<ii>)" using \<W>.simps(2) by auto
      also have "... = caseDistinction True ((\<W> n k \<R> \<ii>) |-| {|\<pi>\<^sup>2 (chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))))|})  (\<W> n k \<R> \<ii>)" using b70 by auto
      then have b7657 :  "\<W>  n (Suc k) \<R> \<ii> = ((\<W> n k \<R> \<ii>) |-| {|\<pi>\<^sup>2 (chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))))|})" using caseDistinction.simps(1) by simp
      show "    \<exists>k0. (k0 < (Suc k) \<and> r |\<in>| \<W> n k0 \<R> \<ii> \<and> r |\<notin>| \<W> n (Suc k0) \<R> \<ii> \<and> chosenUnrealizedRule (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k0 \<R>)) = (\<ii>, r) \<and> (\<ii>, r) \<in> unrealizedRules (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k0 \<R>))) \<and>
         (\<ii>, r) \<in> unrealizedRules (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k0 \<R>))"
      proof (rule disjE)
        from b7657 have "(r |\<notin>|  (\<W> n k \<R> \<ii>)) \<or> (r |\<in>| {|\<pi>\<^sup>2 (chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))))|})" using b59 notin_fset          by blast
        then show "(r |\<notin>|  (\<W> n k \<R> \<ii>)) \<or> (r=  (\<pi>\<^sup>2 (chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))))))" by auto
        {
          assume p1 : "(r=  (\<pi>\<^sup>2 (chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))))))"
          have  "(k < (Suc k) \<and> r |\<in>| \<W> n k \<R> \<ii> \<and> r |\<notin>| \<W> n (Suc k) \<R> \<ii> \<and> chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>)) = (\<ii>, r) \<and> (\<ii>, r) \<in> unrealizedRules (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>))) \<and>
         (\<ii>, r) \<in> unrealizedRules (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>))"
          proof -
            have q1 : "k < Suc k" by arith
            from b70 have b70 : "(((thereIsAnUnrealizedRule  (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))))) \<and>  (\<ii> = chosenSide  (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))))" by auto
            then have "unrealizedRules (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))) \<noteq> {}" using thereIsAnUnrealizedRule_def by auto
            then have g89 : "(chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>))) \<in> (unrealizedRules  (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>)))" using chosenUnrealizedRule_def                  by (simp add: some_in_eq) 
            then obtain i1 r1 where g90 :  "(chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>))) = (i1,r1)" 
              and g91 : "r1 |\<in>| ((\<W> n k \<R>) i1) \<and> (\<not> (realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i1) r1) ((symbol r1)  \<bullet> ((\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>))\<union> {[]}))))" using unrealizedRules_def              by auto 
            then have g93 : "r1 = r" using p1                  by simp 
            from g90 have g94 : "i1 = \<ii>" using chosenSide_def b70 by simp
            from g90 g91 g93 g94 have g98 : "(chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>))) = (\<ii>,r)" and g99 : "r |\<in>| ((\<W> n k \<R>) \<ii>) \<and> (\<not> (realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>) r) ((symbol r)  \<bullet> ((\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>)) \<union> {[]}))))" by auto
            from g99 have q2 : "r |\<in>| \<W> n k \<R> \<ii>"  by auto
            from b59 have q3 : " r |\<notin>| \<W> n (Suc k) \<R> \<ii>" by auto
            have q4 : "chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>)) = (\<ii>, r)" using g98 by auto
            have q5 : "(\<ii>, r) \<in> unrealizedRules (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>))" using g89 g98 by auto
            from q1 q2 q3 q4 q5 show "(k < (Suc k) \<and> r |\<in>| \<W> n k \<R> \<ii> \<and> r |\<notin>| \<W> n (Suc k) \<R> \<ii> \<and> chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>)) = (\<ii>, r) \<and> (\<ii>, r) \<in> unrealizedRules (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>))) \<and>
         (\<ii>, r) \<in> unrealizedRules (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>))" by auto
          qed
          then show "    \<exists>k0. (k0 < (Suc k) \<and> r |\<in>| \<W> n k0 \<R> \<ii> \<and> r |\<notin>| \<W> n (Suc k0) \<R> \<ii> \<and> chosenUnrealizedRule (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k0 \<R>)) = (\<ii>, r) \<and> (\<ii>, r) \<in> unrealizedRules (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k0 \<R>))) \<and>
         (\<ii>, r) \<in> unrealizedRules (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k0 \<R>))"      by blast
        }
        {
          assume "r |\<notin>|  (\<W> n k \<R> \<ii>)"
          hence "    \<exists>k0. (k0 < k \<and> r |\<in>| \<W> n k0 \<R> \<ii> \<and> r |\<notin>| \<W> n (Suc k0) \<R> \<ii> \<and> chosenUnrealizedRule (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k0 \<R>)) = (\<ii>, r) \<and> (\<ii>, r) \<in> unrealizedRules (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k0 \<R>))) \<and>
         (\<ii>, r) \<in> unrealizedRules (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k0 \<R>))"      using Suc.hyps by auto
          then show "    \<exists>k0. (k0 < (Suc k) \<and> r |\<in>| \<W> n k0 \<R> \<ii> \<and> r |\<notin>| \<W> n (Suc k0) \<R> \<ii> \<and> chosenUnrealizedRule (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k0 \<R>)) = (\<ii>, r) \<and> (\<ii>, r) \<in> unrealizedRules (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k0 \<R>))) \<and>
         (\<ii>, r) \<in> unrealizedRules (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k0 \<R>))"            using less_SucI by blast
        }
      qed
    }
  qed
qed
  
  
  
  
  
lemma lemmaPathExistence :
  fixes tr
  fixes I
  assumes "\<Pi> tr \<in>  (image \<Pi> (existential_satisfaction_set I)   )"
  shows  "tr \<in> existential_satisfaction_set I"
  by (smt assms existential_satisfaction_set_def imageE mem_Collect_eq)
    
    
    
lemma entailsStateRule :
  fixes \<ii>
  fixes state
  fixes I
  fixes rule
  fixes \<alpha>
  assumes "entails (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> \<ii>) state) I"
  assumes "state |\<in>| states rule"
  assumes "\<alpha> = symbol rule"
  shows "entails (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) rule) (\<alpha> \<bullet> I)"
proof -
  from assms(1) entails_def existential_satisfaction_set_def have q0 : "\<And> tr . tr \<in> (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> \<ii>) state) \<Longrightarrow> (\<exists> x . x \<in> ((fset (\<Pi> tr)) \<inter> I))" by blast
  have "\<And>tr . tr \<in> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) rule) \<Longrightarrow> tr \<in> existential_satisfaction_set (\<alpha> \<bullet> I)"
  proof -
    fix tr
    assume "tr \<in> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) rule)"
    then obtain parent children where q1 : "tr = NODE parent children" and q2 : "((root tr = symbol rule) \<and> ((fimage (((evaluation (\<A> \<ii>)))) (childrenSet tr)) = states rule))"  by (metis childrenSet.cases language_for_rule_def mem_Collect_eq tree_for_rule_def)
    from q2 obtain child where q3 : "child |\<in>| childrenSet tr" and q4 : "evaluation (\<A> \<ii>) child = state" using assms(2)        by (metis fimageE)
    from q4 have q5 : "child \<in> (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> \<ii>) state)"     by (simp add: language_for_state_def) 
    from q5 q0 obtain x where q6 : "x \<in> I" and q7 : "x \<in> ((fset (\<Pi> child)))"        by (meson IntD1 IntD2)
    from q2 q3 assms(3) notin_fset have "\<alpha>#x \<in> ((fset (\<Pi> tr)))"        by (metis childrenSet.simps paths_def q1 q7 root.simps)
    then show "tr \<in> existential_satisfaction_set (\<alpha> \<bullet> I)" using existential_satisfaction_set_def q6        using prefixLetter_def by auto
  qed
  then show ?thesis using entails_def      by (simp add: entails_def subset_iff) 
qed
  
  
    
    
    
    
section "Main Lemma"
  (*    MAIN LEMMA      *)
  
  (*definition \<alpha> :: "abc" where
   "\<alpha> = (SOME x.(x=x))" *)
  
  
  
  
definition stateSetFromRuleSet where
  "stateSetFromRuleSet ruleSet = (\<Union>| (states |`| (ruleSet)))"
  
  
  
  
lemma z_subset : "Z n l \<subseteq> l"
  by (simp add: Z_def subset_eq)
    
    
    
    
lemma boundedDepthInZ :
  fixes l :: "abc tree fset"
  assumes "l |\<subseteq>| \<Z>\<^sub>\<tau> n UNIV"
  shows "l |\<subseteq>| \<Z>\<^sub>\<tau> n (fset l)"
proof -
  obtain tt :: "abc tree set \<Rightarrow> abc tree set \<Rightarrow> abc tree" where
    "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> x0) = (tt x0 x1 \<in> x1 \<and> tt x0 x1 \<notin> x0)"
    by moura
  then have f1: "(\<not> fset l \<subseteq> Z n (fset l) \<or> (\<forall>t. t \<notin> fset l \<or> t \<in> Z n (fset l))) \<and> (fset l \<subseteq> Z n (fset l) \<or> tt (Z n (fset l)) (fset l) \<in> fset l \<and> tt (Z n (fset l)) (fset l) \<notin> Z n (fset l))"
    by blast
  have f2: "\<forall>t. t \<notin> fset l \<or> t \<in> Z n UNIV"
    by (metis (no_types) \<Z>\<tau>_lemma assms less_eq_fset.rep_eq subset_eq)
  { assume "\<not> (tt (Z n (fset l)) (fset l) \<in> UNIV \<and> height (tt (Z n (fset l)) (fset l)) \<le> n)"
    then have "tt (Z n (fset l)) (fset l) \<notin> fset l \<or> tt (Z n (fset l)) (fset l) \<in> Z n (fset l)"
      using f2 Z_def by blast }
  then have "fset l \<subseteq> Z n (fset l)"
    using f1 Z_def by auto
  then show ?thesis
    by (metis \<Z>\<tau>_lemma less_eq_fset.rep_eq)
qed
  
lemma fbBoundedDepth :
  fixes n
  fixes k
  fixes m
  fixes \<R>
  shows   "\<ff>\<^sub>1 n k \<R> |\<subseteq>| \<Z>\<^sub>\<tau> n UNIV"
proof -
  have b0 : "\<Z>\<^sub>\<tau> n (\<P>\<^sub>\<sigma> (\<R>))|\<subseteq>| \<Z>\<^sub>\<tau> n UNIV" by (metis (no_types) fsubsetI zIntersectLemma)
  have "\<ff>\<^sub>1 n 0 \<R> = \<Z>\<^sub>\<tau> n UNIV" by (simp)
  have b2 : "\<ff>\<^sub>1 n k \<R> |\<subseteq>| \<ff>\<^sub>1 n 0 \<R>"
  proof (induct k)
    show "\<ff>\<^sub>1 n 0 \<R> |\<subseteq>| \<ff>\<^sub>1 n 0 \<R>" by auto
    show "\<And>k. \<ff>\<^sub>1 n k \<R> |\<subseteq>| \<ff>\<^sub>1 n 0 \<R> \<Longrightarrow> \<ff>\<^sub>1 n (Suc k) \<R> |\<subseteq>| \<ff>\<^sub>1 n 0 \<R>"
    proof -
      fix k
      assume k7655 :  "\<ff>\<^sub>1 n k \<R> |\<subseteq>| \<ff>\<^sub>1 n 0 \<R>"
      have k7656 : "\<ff>\<^sub>1 n (Suc k) \<R> |\<subseteq>| \<ff>\<^sub>1 n k \<R>" by (metis dual_order.refl fa_def2 finter_assoc inf.absorb_iff2)
      from k7655 k7656 show "\<ff>\<^sub>1 n (Suc k) \<R> |\<subseteq>| \<ff>\<^sub>1 n 0 \<R>" by auto
    qed
  qed
  from b0 b2 show "\<ff>\<^sub>1 n k \<R> |\<subseteq>| \<Z>\<^sub>\<tau> n UNIV" using \<open>\<ff>\<^sub>1 n 0 \<R> = \<Z>\<^sub>\<tau> n UNIV\<close> order.trans by auto 
qed
  
  
  
  
lemma fSupportsRules :
  fixes p
  fixes n
  fixes \<R>
  fixes i
  assumes b1 : "p |\<in>| \<ff> n  \<R>"
  shows "(satisfiesApproximatorForRuleSet p (\<R> i ) i)"
proof -
  from b1 \<ff>_def have b4 : "p \<in> (\<P> \<R>)" by (metis \<Z>\<tau>_lemma notin_fset subsetCE z_subset) 
  from \<P>_def show "satisfiesApproximatorForRuleSet p (\<R> i) i" using b4 mem_Collect_eq by auto
qed
  
  
  
  
lemma pathsIntersectionLangTree : 
  fixes p
  fixes l
  fixes I
  assumes "fset (\<Pi> p) \<inter> I \<noteq> {}"
  assumes "p |\<in>| l"
  shows "I \<inter> \<Pi>\<^sub>\<tau>\<^sub>F (l) \<noteq> {}"
  using assms(1) assms(2) disjoint_iff_not_equal mem_Collect_eq notin_fset pathsForTreeLanguage_def
proof -
  have f1: "p \<in> fset l"
    by (metis (lifting) assms(2) notin_fset)
  obtain aas :: "'a list set \<Rightarrow> 'a list set \<Rightarrow> 'a list" where
    f2: "\<And>A Aa as Ab Ac. (aas A Aa \<in> A \<or> A \<inter> Aa = {}) \<and> (aas A Aa \<in> Aa \<or> A \<inter> Aa = {}) \<and> ((as::'a list) \<notin> Ab \<or> as \<notin> Ac \<or> Ac \<inter> Ab \<noteq> {})"
    by (metis (no_types) disjoint_iff_not_equal)
  then have f3: "aas (fset (\<Pi> p)) I \<in> I"
    by (metis (lifting) assms(1))
  have "aas (fset (\<Pi> p)) I |\<in>| \<Pi> p"
    using f2 by (meson assms(1) notin_fset)
  then have "I \<inter> {as. \<exists>t. t \<in> fset l \<and> as |\<in>| \<Pi> t} \<noteq> {}"
    using f3 f1 by blast
  then show ?thesis
    using pathsForTreeLanguage_def by blast
qed 
    
    
    
    
lemma orderLemma  :
  fixes n :: nat
  fixes m :: nat
  shows "(n \<le> m) = (n < Suc m)"
  by (simp add: less_Suc_eq_le)
    
    
    
  
lemma pathsForestsTrees:
  fixes l
  shows "\<Pi>\<^sub>\<tau>\<^sub>F ((\<Union>| l)) =  \<Pi>\<^sub>\<phi> (fset l)"
proof -
  from pathsForForestLanguage_def pathsInForest_def 
  have b1 : "\<Pi>\<^sub>\<phi> (fset l) = {p . (\<exists> t \<in> (fset l) . p |\<in>| (\<Union>| (\<Pi> |`| t)))}"    by (smt Collect_cong) 
  have b2 : "\<And> p q. ((p |\<in>| (\<Union>| q)) = (\<exists>pSet. (pSet |\<in>| q \<and> p |\<in>| pSet)))" by auto
  from b2 have b3 : "\<And> p t. ((p |\<in>| (\<Union>| (\<Pi> |`| t))) = (\<exists>pSet. (pSet |\<in>| (\<Pi> |`| t) \<and> p |\<in>| pSet)))" by metis
  have b4 : "\<And> p t. ((\<exists>pSet. (pSet |\<in>| (\<Pi> |`| t) \<and> p |\<in>| pSet)) = (\<exists>tree. (tree |\<in>| t \<and> p |\<in>| ((\<Pi> tree)))))" by auto
  from b3 b4 have b5 : "\<And> p. ((\<exists> t \<in> (fset l) . p |\<in>| (\<Union>| (\<Pi> |`| t))) = (\<exists> t \<in> (fset l). (\<exists>tree. (tree |\<in>| t \<and> p |\<in>| ((\<Pi> tree))))))" by metis
  have b6 : "\<And> p.(\<exists> t \<in> (fset l). (\<exists>tree. (tree |\<in>| t \<and> p |\<in>| ((\<Pi> tree))))) = (\<exists> t \<in> (fset (\<Union>| l)) . p |\<in>| \<Pi> t)"
    by (meson b2 notin_fset) 
  from b2 b3 b4 b5 b6 have b8 : "\<Pi>\<^sub>\<phi> (fset l) = {p . (\<exists> t \<in> (fset (\<Union>| l)) . p |\<in>| \<Pi> t)}"
    using b1 by auto 
  from pathsForTreeLanguage_def have b7 : "\<Pi>\<^sub>\<tau>\<^sub>F ((\<Union>| l)) = {p . (\<exists> t \<in> (fset (\<Union>| l)) . p |\<in>| \<Pi> t)}" by auto
  from b8 b7 show "\<Pi>\<^sub>\<tau>\<^sub>F ((\<Union>| l)) =  \<Pi>\<^sub>\<phi> (fset l)" by auto
      (*using pathsForTreeLanguage_def  pathsForForestLanguage_def pathsInForest_def*) 
qed
  
  
  
lemma stateLanguagesClosedArbitraryOplus :
  fixes \<ii> state
  defines "l == ( ((\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>)) state))"
  shows "closedUnderArbitraryPlus (l)"
proof (simp add :closedUnderArbitraryPlus_def)
  show "\<forall>a. a \<noteq> fempty \<longrightarrow> fset a \<subseteq> l \<longrightarrow> \<Union>| a \<in> l"
  proof
    fix a
      
    show "a \<noteq> fempty \<longrightarrow> fset a \<subseteq> l \<longrightarrow> \<Union>| a \<in> l"
    proof -
      have "a \<noteq> fempty \<Longrightarrow> fset a \<subseteq> l \<Longrightarrow> \<Union>| a \<in> l"
      proof -
        assume n8764654 : "fset a \<subseteq> l"
        assume n75454 : "a \<noteq> fempty"
        then obtain forest where nu6465r : "forest |\<in>| a" by auto
        hence "forest \<in> l" using n8764654          by (meson notin_fset subsetCE) 
        hence "forest \<in> ( ((\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>)) state))" using assms by auto
        then obtain tree where "tree |\<in>| forest" using forest_language_for_state_def by fastforce
        hence n8765654 : "tree |\<in>| \<Union>| a"
          using nu6465r by auto 
            
        have n864543 : "\<And> tree.(tree|\<in>| (\<Union>| a) \<Longrightarrow> evaluation (\<A> \<ii>) tree = state)"
        proof -
          fix tree
          assume "tree|\<in>| (\<Union>| a)"
          then obtain forest where n7645 : "tree |\<in>| forest" and "forest |\<in>| a" using ffUnionLemma by auto
          then have "forest \<in> l" using n8764654 notin_fset            by fastforce 
          hence "forest \<in> ( ((\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>)) state))" using assms by auto
          then show " evaluation (\<A> \<ii>) tree = state" using forest_language_for_state_def n7645            by (simp add: forest_language_for_state_def) 
        qed
        show "\<Union>| a \<in> l"  
        proof (simp add : assms)
          
          from n864543 n8765654 show " \<Union>| a \<in> \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>) state" using forest_language_for_state_def
            by (smt mem_Collect_eq)
        qed
      qed
      then show "a \<noteq> {||} \<longrightarrow> fset a \<subseteq> l \<longrightarrow> \<Union>| a \<in> l" by simp
    qed
  qed
qed
  
  
  
            
            
              
  
lemma stateLanguagesClosedOplus :
  fixes \<ii> state
  defines "l == ( ((\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>)) state))"
  shows "closedUnderPlus (l)"
proof -
  have b5 : "\<And> a b.(a \<in> l \<Longrightarrow> b \<in> l \<Longrightarrow> plus a b \<in> l)"
  proof -
    fix a b
    assume b2 : "a \<in> l" and b3 : "b \<in> l"
    from b2 b3 have b7 : "\<And> tree.(tree|\<in>|(plus a b) \<Longrightarrow> evaluation (\<A> \<ii>) tree = state)"
    proof -
      fix tree
      assume b10 : "tree|\<in>|(plus a b)"
      from b10 plus_def have b11 : "tree|\<in>|a \<or> tree|\<in>|b" by blast
      from b2 b3 forest_language_for_state_def b11 show "evaluation (\<A> \<ii>) tree = state" using l_def mem_Collect_eq
        by fastforce 
    qed
    from b7 b2 b3 forest_language_for_state_def l_def show b4 : "plus a b \<in> l" using mem_Collect_eq      by (smt funionCI plusComm plus_def) 
  qed
  from b5 closedUnderPlus_def show ?thesis by metis
qed
  
  
lemma \<P>\<sigma>_mono :
  fixes Sa1 Sa2
  assumes "\<And> i . (Sa1 i |\<subseteq>| Sa2 i)"
  shows "(\<P>\<^sub>\<sigma> Sa1) \<subseteq> (\<P>\<^sub>\<sigma> Sa2)"
proof 
  fix x
  assume "x \<in> \<P>\<^sub>\<sigma> Sa1"
  then have "\<And> \<ii> . (\<forall> p \<in> (pathsInTree x) .        (\<exists> r  . \<exists>rule \<in> (fset (Sa1 \<ii>)) . ((stateFromRule  \<ii> (hd r)) |\<in>| (states rule)) \<and>                      (pathFitsListAndListIsARun \<ii> p r)))" using \<P>\<^sub>\<sigma>_def satisfiesApproximatorForStatesFromRuleSet_def pathSatisfiesApproximatorForStateFromRuleSet_def by blast
  then have "\<And> \<ii> . (\<forall> p \<in> (pathsInTree x) .        (\<exists> r  . \<exists>rule \<in> (fset (Sa2 \<ii>)) . ((stateFromRule  \<ii> (hd r)) |\<in>| (states rule)) \<and>                      (pathFitsListAndListIsARun \<ii> p r)))" using assms notin_fset    by (metis less_eq_fset.rep_eq subsetCE) 
  then show "x \<in> \<P>\<^sub>\<sigma> Sa2" by (simp add: \<P>\<^sub>\<sigma>_def pathSatisfiesApproximatorForStateFromRuleSet_def satisfiesApproximatorForStatesFromRuleSet_def) 
qed
  
  
  
  
  
  
  
  
lemma piFset  :
  shows "\<And>l. \<Pi>\<^sub>\<tau>\<^sub>F l = (fset (\<Pi>\<^sub>\<iota>\<^sub>\<phi> l))"
proof -
  fix l
  from pathsForTreeLanguage_def have   "\<Pi>\<^sub>\<tau>\<^sub>F l = {p . (\<exists> t \<in> fset (l) . p |\<in>| \<Pi> t)}" by auto
  then have a1: "\<And>p. p \<in> \<Pi>\<^sub>\<tau>\<^sub>F l = (\<exists> t \<in> fset (l) . p |\<in>| \<Pi> t)" by auto
  from pathsTreeForest have "\<And>p. (p |\<in>| pathsInForest l) = (\<exists> tr. (tr |\<in>| l \<and> p |\<in>| \<Pi> tr))" by auto
  then have a2 :"\<And>p. (p \<in> (fset (\<Pi>\<^sub>\<iota>\<^sub>\<phi> l))) = (\<exists> tr. (tr |\<in>| l \<and> p |\<in>| \<Pi> tr))"        by (meson notin_fset)
  from a1 a2 notin_fset show "\<Pi>\<^sub>\<tau>\<^sub>F l = (fset (\<Pi>\<^sub>\<iota>\<^sub>\<phi> l))"        by (metis subsetI subset_antisym) 
qed
  
  
    
lemma heightContainLemma :
  assumes "(\<Pi> t |\<subseteq>| \<Pi> s)"
  shows "(\<Pi> t) \<in> ((image \<Pi> {t . height t > n})) \<Longrightarrow> (\<Pi> s) \<in> (image \<Pi> {t . height t > n})"
  using heightOnlyDependsOnPaths maxMonotonic  by (smt assms dual_order.strict_implies_order fimage_mono imageE image_eqI leD le_trans mem_Collect_eq order.not_eq_order_implies_strict)
    
    
    
lemma satisfiesPiContain:
  assumes "(\<Pi> t |\<subseteq>| \<Pi> s)"
  assumes "(\<Pi> t) \<in> ( (image \<Pi> (existential_satisfaction_set I)   ))"
  shows "(\<Pi> s) \<in> ( (image \<Pi> (existential_satisfaction_set I )))  "
proof -
  have "t \<in> (existential_satisfaction_set I)   "    by (simp add: assms(2) lemmaPathExistence)
  then have "s \<in> (existential_satisfaction_set I)   " using assms(1) existential_satisfaction_set_def        by (smt Int_iff less_eq_fset.rep_eq mem_Collect_eq subsetCE)
  then show ?thesis by blast
qed
  
lemma vUpwardsClosedLemma :
  assumes  "(\<Pi> t) \<in> ((upwardClosure (image \<Pi> (((Z \<N> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) (hd r))))))) 
                                 \<union> (image \<Pi> {t . height t > \<N>})) 
                              \<inter> (\<Inter>I \<in> (necess (\<A> \<ii>) \<I> (hd r)) . (image \<Pi> (existential_satisfaction_set I)   ))"
  assumes "(\<Pi> t |\<subseteq>| \<Pi> s)"
  shows "(\<Pi> s) \<in> ((upwardClosure (image \<Pi> (((Z \<N> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) (hd r))))))) 
                                 \<union> (image \<Pi> {t . height t > \<N>})) 
                              \<inter> (\<Inter>I \<in> (necess (\<A> \<ii>) \<I> (hd r)) . (image \<Pi> (existential_satisfaction_set I)   ))"
proof 
  from assms have u1 : "(\<Pi> t) \<in> ((upwardClosure (image \<Pi> (((Z \<N> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) (hd r))))))) 
                                 \<union> (image \<Pi> {t . height t > \<N>}))" by auto
  from assms upwardClosure_def have u2 : "(\<Pi> t) \<in> ((upwardClosure (image \<Pi> (((Z \<N> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) (hd r)))))))) \<Longrightarrow> (\<Pi> s) \<in> ((upwardClosure (image \<Pi> (((Z \<N> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) (hd r))))))))"
    by (smt less_eq_fset.rep_eq mem_Collect_eq subsetCE subsetI)
  from assms(2) have u3 : "(\<Pi> t) \<in> ((image \<Pi> {t . height t > \<N>})) \<Longrightarrow> (\<Pi> s) \<in> (image \<Pi> {t . height t > \<N>})" using heightContainLemma by blast
  from u1 u2 u3      show " \<delta>\<^sub>\<tau> s \<in> upwardClosure (\<delta>\<^sub>\<tau>\<^sub>\<lambda> (Z \<N> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) (hd r)))) \<union> \<delta>\<^sub>\<tau>\<^sub>\<lambda> {t. \<N> < height t}" by auto
  from assms have "(\<Pi> t) \<in> (\<Inter>I \<in> (necess (\<A> \<ii>) \<I> (hd r)) . (image \<Pi> (existential_satisfaction_set I)   ))" by blast
  then have "\<And> I . (I \<in> (necess (\<A> \<ii>) \<I> (hd r)))  \<Longrightarrow> (\<Pi> t) \<in> ( (image \<Pi> (existential_satisfaction_set I)   ))" by blast
  then have "\<And> I . (I \<in> (necess (\<A> \<ii>) \<I> (hd r)))  \<Longrightarrow> (\<Pi> s) \<in> ( (image \<Pi> (existential_satisfaction_set I)   ))" using assms(2) satisfiesPiContain by blast
  then show "(\<Pi> s) \<in> (\<Inter>I \<in> (necess (\<A> \<ii>) \<I> (hd r)) . (image \<Pi> (existential_satisfaction_set I)   ))" by blast
qed
  
  
  
  
lemma  lemmaUnionUnion :
  shows  " \<Union>| (mapping |`| (\<Union>| ((\<lambda>symbol. selector symbol) |`| rootSymbols))) = \<Union>| ((\<lambda>symbol. \<Union>| (mapping |`| selector symbol)) |`| rootSymbols)" 
proof 
  show "\<Union>| (mapping |`| \<Union>| (selector |`| rootSymbols)) |\<subseteq>| \<Union>| ((\<lambda>symbol. \<Union>| (mapping |`| selector symbol)) |`| rootSymbols)"
    by fastforce 
  show "\<Union>| ((\<lambda>symbol. \<Union>| (mapping |`| selector symbol)) |`| rootSymbols) |\<subseteq>| \<Union>| (mapping |`| \<Union>| (selector |`| rootSymbols))" by fastforce 
qed
  
  
  
lemma pathE : "\<And>tree . path |\<in>| \<delta>\<^sub>\<tau> tree = (\<exists> tail. path = (root tree)#tail \<and> tail  |\<in>| (pathsInForest (childrenSet tree)) |\<union>| (finsert [] fempty))" 
proof -
  fix tree :: "abc tree"
  show "path |\<in>| \<delta>\<^sub>\<tau> tree = (\<exists> tail. path = (root tree)#tail \<and> tail  |\<in>| (pathsInForest (childrenSet tree)) |\<union>| (finsert [] fempty))" 
  proof (simp add : pathAlternateDef pathsInForest_def)
    
    from tree.exhaust obtain roota childrena where n76687 : "tree = (NODE roota childrena)" by blast
        
    from n76687 have " (path |\<in>| \<delta>\<^sub>\<tau> tree) = (\<exists>tail. path = roota  # tail \<and> (tail = [] \<or> fBex (childrena) (\<lambda>x. tail |\<in>| \<delta>\<^sub>\<tau> x)))"
      using childrenSet.simps eq_fmem_trans fBexE fBex_cong fBex_triv_one_point1 fBex_triv_one_point2 rev_fBexI by fastforce
        
    then show "(path |\<in>| \<delta>\<^sub>\<tau> tree) = (\<exists>tail. path = root tree # tail \<and> (tail = [] \<or> fBex (childrenSet tree) (\<lambda>x. tail |\<in>| \<delta>\<^sub>\<tau> x)))"  using root.simps childrenSet.simps  n76687
      by (simp add: pathsInForest_def) 
  qed
qed
  
    
    
    
lemma pathsContainment:
  assumes "\<Pi>\<^sub>\<iota>\<^sub>\<phi>  x1 |\<union>| (finsert [] fempty) |\<subseteq>| ((\<Pi>\<^sub>\<iota>\<^sub>\<phi>  x2 |\<union>| (finsert [] fempty)))"
  shows "\<Pi>\<^sub>\<iota>\<^sub>\<phi>  x1  |\<subseteq>| (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  x2)"
proof 
  fix x
  assume n65898 : "x |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> x1"
  hence "x |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi>  x1 |\<union>| (finsert [] fempty)" by auto
  hence "x |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi>  x2 |\<union>| (finsert [] fempty)" using assms(1) by auto
  hence "x |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi>  x2 \<or> x = []"    by blast    
  from n65898 noEmptyPathsInPi pathsInForest_def have "x \<noteq> []"
    by (metis list.distinct(1) pathsTreeForest) 
  show "x |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi>  x2"
    using \<open>x \<noteq> []\<close> \<open>x |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> x2 \<or> x = []\<close> by blast 
qed
  
                
    
lemma heightSingleton : 
  assumes "maxFset (height |`| x) \<le> n"
  shows " {|NODE \<alpha> x|} |\<in>| boundedForests (Suc n)"
proof -
  have "{|NODE \<alpha> x|} \<in> fset (boundedForests (Suc n))"
    by (simp add : restrictionIsFiniteForests assms(1))
  then show ?thesis using notin_fset
    by fastforce
qed
  
  
lemma fixOplusRulesRoot :
  fixes i \<R>
  assumes "originalForest \<in> \<Oplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R>)"
  assumes "\<And> rule . rule |\<in>| \<R> \<Longrightarrow> symbol rule = \<alpha>"
  assumes "x |\<in>| originalForest"
  shows "root x = \<alpha>"
  using bigoplusForests_def  forest_language_for_rule_def tree_for_rule_def
  by (smt assms(1) assms(2) assms(3) biguplusForests_def fimageE mem_Collect_eq) 
  
  
lemma stateRuleSet :
  assumes "state |\<in>| states rule"
assumes "    rule |\<in>| \<R> "
shows "state |\<in>| stateSetFromRuleSet (\<R> )"
  using stateSetFromRuleSet_def
  using assms(1) assms(2) by fastforce 
    
lemma singletonRuleLang :
  assumes "tr \<in> \<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) state"
    shows "(finsert tr fempty) \<in> \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) state"
  using assms forest_language_for_state_def language_for_state_def by fastforce 

  
    
  
lemma heightBoundedPaths :
  assumes "\<Pi>\<^sub>\<iota>\<^sub>\<phi> x = \<Pi>\<^sub>\<iota>\<^sub>\<phi> y"
  assumes " x |\<in>| boundedForests n"
  shows "y |\<in>| boundedForests n"
proof -
  from assms(2) have "x \<in> fset ( boundedForests n)" using notin_fset by fastforce
  hence  "x \<in> {f. \<forall>t. t |\<in>| f \<longrightarrow> height t \<le> n}" using restrictionIsFiniteForests by auto
  hence "\<And> tr . tr |\<in>| x \<Longrightarrow> height tr \<le> n" by auto
  hence "\<And> path tr . tr |\<in>| x \<Longrightarrow> path |\<in>| \<Pi> tr \<Longrightarrow> length path \<le> n" using heightOnlyDependsOnPaths
    by (metis dual_order.trans fimage_eqI finiteMaxExists(1)) 
  hence "\<And> path . path |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> x \<Longrightarrow> length path \<le> n" using pathsInTree_def
    by (metis pathsTreeForest) 
  hence "\<And> path . path |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> y \<Longrightarrow> length path \<le> n" using assms(1) by auto
  hence "\<And> path tr . tr |\<in>| y \<Longrightarrow> path |\<in>| \<Pi> tr \<Longrightarrow> length path \<le> n" using pathsInTree_def
    using pathsTreeForest by fastforce 
  hence "\<And> tr . tr |\<in>| y \<Longrightarrow> height tr \<le> n" using heightOnlyDependsOnPaths
    by (metis fimageE finiteMaxExists(2) finiteMaxExists(3) le_zero_eq nat_le_linear) 
  hence "y \<in> fset ( boundedForests n)" using restrictionIsFiniteForests  by auto
  then show "y |\<in>| boundedForests n" using notin_fset by fastforce
qed
  
  
lemma suffixSets :
  fixes symbol
  assumes "  ((\<lambda> x. symbol#x) |`| a) |\<subseteq>|  ((\<lambda> x. symbol#x) |`| b)"
  shows "a |\<subseteq>| b"
proof 
  fix x
  assume "x |\<in>| a"
  hence "symbol#x |\<in>| ((\<lambda> x. symbol#x) |`| b)" using assms by auto
  then show "x |\<in>| b"
    by auto 
qed
  
  
    
    
lemma rootsPaths :
  shows "\<Pi>\<^sub>\<iota>\<^sub>\<phi> otherForest1 |\<subseteq>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> otherForest2 \<Longrightarrow> root |`| otherForest1 |\<subseteq>| root |`| otherForest2"
proof (simp add :pathsInForest_def)
  show " \<Union>| (\<Pi> |`| otherForest1) |\<subseteq>| \<Union>| (\<Pi> |`| otherForest2) \<Longrightarrow> root |`| otherForest1 |\<subseteq>| root |`| otherForest2"
  proof -
    assume n76578767 : " \<Union>| (\<Pi> |`| otherForest1) |\<subseteq>| \<Union>| (\<Pi> |`| otherForest2)"
    show "root |`| otherForest1 |\<subseteq>| root |`| otherForest2" 
    proof
      show "\<And>x. x |\<in>| root |`| otherForest1 \<Longrightarrow> x |\<in>| root |`| otherForest2"
      proof -
        fix x
        assume "x |\<in>| root |`| otherForest1"
        obtain tree where "x = root tree" and ny6r5t7 : "tree |\<in>| otherForest1"
          using \<open>x |\<in>| root |`| otherForest1\<close> by blast 
        then have "[x] |\<in>| \<Pi> tree" using rootIsPath root.simps  by (metis tree.exhaust) 
        then have "[x] |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> otherForest2" using pathsInForest_def ny6r5t7 n76578767
          by fastforce 
        then obtain tree2 where "[x] |\<in>| \<Pi> tree2" and n6556897 : "tree2 |\<in>| otherForest2" using pathsInForest_def
          using pathsTreeForest by blast 
        then have "root tree2 = x" using \<Pi>.simps tree.exhaust root.simps
          using noEmptyPathsInPi by fastforce 
        then show "x |\<in>| root |`| otherForest2" using n6556897
          by blast 
      qed
    qed
  qed
qed
  
  
  
lemma pathForestEmpty :
  assumes "\<Pi>\<^sub>\<iota>\<^sub>\<phi> (otherForest2) = fempty"
  shows "otherForest2 = fempty"
proof -
  have "\<And>x . x |\<in>| otherForest2 \<Longrightarrow> [root x] |\<in>| \<Pi> x" using rootIsPath2 by auto
  hence "\<And>x . x |\<in>| otherForest2 \<Longrightarrow> [root x] |\<in>| pathsInForest otherForest2" using pathsInForest_def by blast
  hence "\<And>x . x |\<in>| otherForest2 \<Longrightarrow> \<Pi>\<^sub>\<iota>\<^sub>\<phi> (otherForest2) \<noteq> fempty" by auto
  then show "otherForest2 = fempty" using assms by auto
qed
  
lemma dependentChoice :
  assumes "\<And>x . \<exists> y. P x y"
  obtains choice where "\<And>x . P x (choice x)"
proof -
  def choice == "\<lambda> x. SOME y . P x y"
  then  have "\<And>x . P x (choice x)" using assms(1)    by (simp add: someI_ex) 
  then show "(\<And>choice. (\<And>x. P x (choice x)) \<Longrightarrow> thesis) \<Longrightarrow> thesis" by auto
qed
  
       
lemma psiDef :
  shows "psi (NODE symbol1 children1)
      = NODE symbol1 (fimage (\<lambda> symbol2 .
                              psi (NODE symbol2 (\<Union>| (fimage childrenSet (childrenWithSymbol symbol2 children1)))
                                  )
                              )
                              (fimage root children1)
                     )"
    sorry
(*  using CombinatoricsBackground.psi.simps by blast*)
    
    
    
 
  (*lemma smaller_than_max_aux :
  fixes n :: nat
  fixes y :: nat
  shows "(\<forall> (x :: nat fset) . size x = n \<longrightarrow> (y |\<in>| x \<longrightarrow> y \<le> (ffold max 0 x)))"
proof (induction n)
  show " \<And> n. \<forall>x. size x = n \<longrightarrow> y |\<in>| x \<longrightarrow> y \<le> ffold max 0 x \<Longrightarrow>
         \<forall>x. size x = Suc n \<longrightarrow> y |\<in>| x \<longrightarrow> y \<le> ffold max 0 x" sorry
  show "\<forall>(x :: nat fset). size x = 0 \<longrightarrow> y |\<in>| x \<longrightarrow> y \<le> ffold max 0 x" sorry*)
  (*proof
fix x :: "nat fset"
assume 0: "size x = 0"
assume 1: "y |\<in>| x"
from 0 have 2: "x = {||}" sorry
from 2 have 3: "y |\<notin>| x" by blast
from 1 3 have 4: "False" by blast
from 4 have  "y \<le> ffold max 0 x" by blast
from 1 4 have 5: "y |\<in>| x \<longrightarrow> y \<le> ffold max 0 x" by blast
from 0 5 have "size x = 0 \<longrightarrow> y |\<in>| x \<longrightarrow> y \<le> ffold max 0 x" by blast
have ?thesis sorry
qed*)
  (*qed*)
  
  (*lemma smaller_than_max:
  fixes y :: nat
  fixes x :: "nat fset"
  shows "y |\<in>| x \<longrightarrow> y \<le> (ffold max 0 x)"
  sorry*)
  (*proof -
def n == "size x"
from smaller_than_max_aux have "(\<forall> (x :: nat fset) . size x = n \<longrightarrow> (y |\<in>| x \<longrightarrow> y \<le> (ffold max 0 x)))" by blast
from this have "size x = n \<longrightarrow> (y |\<in>| x \<longrightarrow> y \<le> (ffold max 0 x))" by blast
with n_def this show ?thesis by blast
qed*)
  
  (*
lemma children_smaller_depth :
  fixes x :: "'L tree"
  fixes y :: "'L tree"
  assumes "y |\<in>| childrenSet x"
  shows "height x \<ge> 1 + height y"
  sorry*)
  (*proof -
from height_def have 1 : "height x = 1 + (ffold max 0 (fimage height (childrenSet x)))" sorry
from smaller_than_max have "(ffold max 0 (fimage height (childrenSet x))) \<ge> height y" by blast
from this have "1 + (ffold max 0 (fimage height (childrenSet x))) \<ge> 1 + height y" by arith
from 1 this have "height x \<ge> Suc (height y)" by arith
thus ?thesis by arith
qed*)
    
end
  