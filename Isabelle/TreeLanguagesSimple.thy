theory TreeLanguagesSimple
  imports Main "$ISABELLE_HOME/src/HOL/Library/FSet" "$ISABELLE_HOME/src/HOL/Orderings" CombinatoricsBackground BasicLemmas
begin
  
  
  (* ============================================= *)
section "Path Set Approximators"
  
  
lemma singletonLanguage:
  shows "tree \<in>  \<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) rule \<Longrightarrow> (finsert tree fempty) \<in> \<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) rule"
  by (simp add: forest_language_for_rule_def language_for_rule_def) 
    
lemma treeSatisfiesSomeRule :
  shows "\<exists> rule . tree \<in> \<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) rule"
proof (simp add : language_for_rule_def tree_for_rule_def)
  show "\<exists>rule. root tree = symbol rule \<and> evaluation (\<A> i) |`| childrenSet tree = states rule"
    by (metis rule.select_convs(1) rule.select_convs(2)) 
qed
  
  
  
    
lemma rootOfV :
  fixes path ruleSeq \<ii> \<alpha>
  assumes a1 : "(( (down (hd path))) \<in> ( \<V>\<^sub>\<tau> \<ii> (hd ruleSeq)  )   ) "
  assumes a2 : "symbol (hd ruleSeq) = \<alpha>"
  shows "root (down (hd path)) = \<alpha>"
proof -
  def t == "(down (hd path))"
  then show "root (down (hd path)) = \<alpha>" using a2 t_def a1 t_def \<V>\<^sub>\<tau>_def by blast
qed
  
  
lemma languagesSatisfyV :
  assumes "tree \<in> \<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) rule" 
  shows "tree \<in> \<V>\<^sub>\<tau> i rule" 
proof (simp add :\<V>\<^sub>\<tau>_def)
  from assms have n67543e5 : "root tree = symbol rule" using language_for_rule_def  tree_for_rule_def by blast
  have n67543e5b : "(\<delta>\<^sub>\<tau> tree \<in> upwardClosure (\<delta>\<^sub>\<tau>\<^sub>\<lambda> (Z \<N> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) rule))) \<or> \<delta>\<^sub>\<tau> tree \<in> \<delta>\<^sub>\<tau>\<^sub>\<lambda> {t. \<N> < height t})"
  proof -
    have "height tree \<le> \<N> \<or> \<N> < height tree" by auto
    hence "tree \<in> {t. \<N> < height t} \<or> tree \<in> Z \<N> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) rule)" using Z_def assms by fastforce
    hence "\<delta>\<^sub>\<tau> tree \<in> \<delta>\<^sub>\<tau>\<^sub>\<lambda> (Z \<N> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) rule)) \<or> \<delta>\<^sub>\<tau> tree \<in> \<delta>\<^sub>\<tau>\<^sub>\<lambda> {t. \<N> < height t}" by auto
    then show "\<delta>\<^sub>\<tau> tree \<in> upwardClosure (\<delta>\<^sub>\<tau>\<^sub>\<lambda> (Z \<N> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) rule))) \<or> \<delta>\<^sub>\<tau> tree \<in> \<delta>\<^sub>\<tau>\<^sub>\<lambda> {t. \<N> < height t}" using upwardClosure_def by auto
  qed
  have "\<And>x. x \<in>necess (\<A> i) \<I> rule \<Longrightarrow> \<delta>\<^sub>\<tau> tree \<in> \<delta>\<^sub>\<tau>\<^sub>\<lambda> (existential_satisfaction_set x)"
  proof -
    fix x
    assume "x\<in>necess (\<A> i) \<I> rule"
    hence "x \<in> op \<bullet> (symbol rule) ` {I \<in> \<I>. \<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) rule \<subseteq> existential_satisfaction_set (symbol rule \<bullet> I)}" using necess_def by blast
    then obtain I where "I \<in> \<I>" and "\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) rule \<subseteq> existential_satisfaction_set (symbol rule \<bullet> I)" and "x = (symbol rule) \<bullet> I" by blast
    hence "\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) rule \<subseteq> existential_satisfaction_set x" by auto
    hence "tree \<in> existential_satisfaction_set x" using assms by auto
    then show "\<delta>\<^sub>\<tau> tree \<in> \<delta>\<^sub>\<tau>\<^sub>\<lambda> (existential_satisfaction_set x)" by auto
  qed
  then show "root tree = symbol rule \<and>
    (\<delta>\<^sub>\<tau> tree \<in> upwardClosure (\<delta>\<^sub>\<tau>\<^sub>\<lambda> (Z \<N> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) rule))) \<or> \<delta>\<^sub>\<tau> tree \<in> \<delta>\<^sub>\<tau>\<^sub>\<lambda> {t. \<N> < height t}) \<and> (\<forall>x\<in>necess (\<A> i) \<I> rule. \<delta>\<^sub>\<tau> tree \<in> \<delta>\<^sub>\<tau>\<^sub>\<lambda> (existential_satisfaction_set x))" using n67543e5 n67543e5b by auto
qed
  
  
  
lemma gInFPre : 
  assumes "\<And> \<R>  r i. (r |\<in>| \<R> i \<Longrightarrow> (r |\<in>| rule_set (\<A> i)))"
  shows "\<And> (\<R> :: ot \<Rightarrow> (stt,abc) rule fset) x . x \<in> ((\<Uplus> ( ((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i)) |`| (((\<R>) i)))))) \<Longrightarrow> (fset x) \<subseteq> (\<P>\<^sub>1 \<R> i)"
proof (simp add : \<P>\<^sub>1_def satisfiesApproximatorForRuleSet_def)
  
  have  "\<And>\<R> x tree p. x \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i) \<Longrightarrow> tree |\<in>| x \<Longrightarrow>  p \<in>pathsInTree tree \<Longrightarrow> pathSatisfiesApproximatorForRuleSet p (\<R> i) i"
  proof -
    fix p
    show "\<And>\<R> x tree. x \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i) \<Longrightarrow> tree |\<in>| x \<Longrightarrow>  p \<in>pathsInTree tree \<Longrightarrow> pathSatisfiesApproximatorForRuleSet p (\<R> i) i"
    proof (induct p)
      case Nil
      then show ?case using noEmptyPaths  pathsInTree_def by auto
    next
      case (Cons a p)
      fix x
      assume n7546 : "x \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i)"
      hence n764354 : " \<forall>tr. tr |\<in>| x \<longrightarrow> (\<exists>lang. lang |\<in>| (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i) \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> lang))" using biguplusForests_def by blast
          
      fix tree
      assume n54766 : " tree |\<in>| x "
      from n764354 n54766 obtain subforest rule where "tree |\<in>| subforest" and "subforest |\<subseteq>| x" and "subforest \<in> \<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) rule" and n654654 :  "rule |\<in>| \<R> i" by blast
      hence n875654 : "tree \<in> \<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) rule"            by (simp add: forest_language_for_rule_def language_for_rule_def) 
      hence n65897 : "tree \<in> \<V>\<^sub>\<tau> i rule"  using languagesSatisfyV by auto
          
          
          
      assume "(Cons a p) \<in>pathsInTree tree"
      hence n67587 : "isAPathp (Cons a p)" and "(\<exists>e1 tail. (Cons a p) = e1 # tail \<and> down e1 = tree)" using pathsInTree_def by auto
      hence n5457 : "down a = tree" by auto
          
      show "pathSatisfiesApproximatorForRuleSet (Cons a p) (\<R> i) i"
      proof (simp add : pathSatisfiesApproximatorForRuleSet_def)
        
        have "\<exists>r. hd r = rule \<and> pathFitsListAndListIsARun i (a # p) r"
        proof (rule disjE)
          from n67587 show  "((\<exists>node. (Cons a p) = [node]) \<or> (\<exists>path e2. (Cons a p) = e2 # path \<and> isAPathp path \<and> (\<exists>e1 tail. path = e1 # tail \<and> immediatelyDominates e2 e1)))" using isAPathp.simps by blast
          have a1 : "labelOfNode a = symbol rule" using n875654 language_for_rule_def tree_for_rule_def
            using labelOfNode_def n5457 rootRule by fastforce 
          from assms n654654 have a2 : "rule |\<in>| rule_set (\<A> i)" by auto
          from n5457 n875654 have a3 : "down a \<in> \<V>\<^sub>\<tau> i rule" using languagesSatisfyV by auto
              
              
          {
            assume n764544 : "(\<exists>path e2. (Cons a p) = e2 # path \<and> isAPathp path \<and> (\<exists>e1 tail. path = e1 # tail \<and> immediatelyDominates e2 e1))"
            hence n764654 : "isAPathp p" by blast
            from n764544 obtain e1 tail where n65798 : "p = e1#tail" and n454576 : "immediatelyDominates a e1" by auto
            from immediatelyDominates_def have n754654 : "down e1 |\<in>| childrenSet tree" using n5457 n454576 by auto
            from language_for_rule_def n875654 have "tree_for_rule (\<A> i) rule tree" by auto
            hence "(evaluation (\<A> i) |`| childrenSet tree = states rule)" using tree_for_rule_def by metis
            then obtain state where n6564387 : "evaluation (\<A> i) (down e1) = state" and n545877 : "state |\<in>| states rule" using n754654 by blast
            obtain ruleDown where n754655 : " (down e1) \<in> \<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) ruleDown" using treeSatisfiesSomeRule by auto
            def forestDown == "(finsert (down e1) fempty)"
            have n75456 : "forestDown \<in> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) ruleDown)" using n754655 forestDown_def using singletonLanguage by auto
            def \<R>Down == "\<lambda> (i :: ot). (finsert ruleDown fempty)"
            from \<R>Down_def n75456 biguplusForests_def have n5487 : "forestDown \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R>Down i)" by auto
            have n568 : " p \<in> pathsInTree (down e1)" 
            proof (simp add : pathsInTree_def)
              from n65798 have "(( p = e1#tail) \<and> down e1 = down e1)" by auto
              hence "(\<exists>e1a. (\<exists>tail. p = e1a # tail) \<and> down e1a = down e1)" by auto
              then show "isAPathp p \<and> (\<exists>e1a. (\<exists>tail. p = e1a # tail) \<and> down e1a = down e1)" using n764654 by auto
            qed
            from Cons.hyps have "forestDown \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R>Down i) \<Longrightarrow> (down e1) |\<in>| forestDown \<Longrightarrow> p \<in> pathsInTree (down e1) \<Longrightarrow> pathSatisfiesApproximatorForRuleSet p (\<R>Down i) i" by auto
            hence n753545 :  "pathSatisfiesApproximatorForRuleSet p (\<R>Down i) i" using n568 n5487 forestDown_def by auto
            from n753545 pathSatisfiesApproximatorForRuleSet_def obtain r rTail where n646785687 : "hd r |\<in>| (\<R>Down i) \<and> pathFitsListAndListIsARun i p r" by metis
            from n646785687  have "hd r |\<in>| (\<R>Down i)" by auto
            hence n65t6988 : "hd r = ruleDown" using \<R>Down_def by auto
            from n65798 pathFitsListAndListIsARun.simps n646785687 obtain rHead rTail where n75465 : "r = rHead#rTail"
              by (metis hd_Cons_tl) 
            hence n6587 : "rHead = hd r" using n646785687 by auto
                
            from n65t6988  n6587  have n65687 : "ruleDown = rHead" by auto
                
            have y1 : "hd (rule#r) = rule" by auto
            have y2 : "pathFitsListAndListIsARun i (a # p) (rule#r)"
            proof (simp add : pathFitsListAndListIsARun.simps(3))
              from n5457 a3 rootOfV labelOfNode_def have x1 : "labelOfNode a = symbol rule"   using a1 by blast 
              have x2 : "rule |\<in>| rule_set (\<A> i)" using assms n654654 by auto
              from n65897 n5457 have x3 : "down a \<in> \<V>\<^sub>\<tau> i rule" by auto
              from n646785687 have x4 : " pathFitsListAndListIsARun i p r" by blast
                  
                  
              from  n6564387 have   "evaluation (\<A> i) (down e1) = state" by auto
              from  n545877 have   "state |\<in>| states rule" by blast
              from n754655 have " (down e1) \<in> \<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) ruleDown" by auto
                  
                  
              from n75456  have n767097 : "forestDown \<in> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) ruleDown)" by auto
              from n6564387 have n6545787 : "evaluation (\<A> i) (down e1) = state" by auto
              from n754655 n767097 n6545787 evaluation_def language_for_rule_def tree_for_rule_def have " tree_for_rule (\<A> i) ruleDown (down e1)" by auto
              hence n653545 : "evaluation (\<A> i) |`| childrenSet  (down e1) = states ruleDown" using tree_for_rule_def by metis
                  have n65764 : "(down e1) = (NODE (root (down e1)) (childrenSet  (down e1)))"
                    by (metis (no_types) childrenSet.cases childrenSet.simps root.simps) 
                  
                  
                  from n6545787 language_for_rule_def have "evaluation (\<A> i) (down e1) = state" by auto
                  hence n5t45789 : "state = (((transition (\<A> i)) (fimage (evaluation (\<A> i)) (childrenSet  (down e1)))) (root (down e1)))" using n65764 evaluation.simps by metis
                   from n653545   have n54458797 : "(states ruleDown) = (fimage (evaluation (\<A> i)) (childrenSet  (down e1)))"  by auto
                      
                       have n5865654 : "(root (down e1)) = (symbol ruleDown)" using n754655 language_for_rule_def tree_for_rule_def by blast
                       
              from n54458797 n5t45789 n5865654 have "(transition (\<A> i) (states ruleDown) (symbol ruleDown) = state)"  by auto
                  
              have x5 : "(\<forall>h. (\<exists>t. r = h # t) \<longrightarrow> transition (\<A> i) (states h) (symbol h) |\<in>| states rule)"
                using \<open>transition (\<A> i) (states ruleDown) (symbol ruleDown) = state\<close> n545877 n65t6988 by auto 
                  
              from x1 x2 x3 x4 x5 show "labelOfNode a = symbol rule \<and> rule |\<in>| rule_set (\<A> i) \<and> down a \<in> \<V>\<^sub>\<tau> i rule \<and> pathFitsListAndListIsARun i p r \<and> (\<forall>h. (\<exists>t. r = h # t) \<longrightarrow> transition (\<A> i) (states h) (symbol h) |\<in>| states rule) " by auto
            qed
            from y1 y2  show "\<exists>r. hd r = rule \<and> pathFitsListAndListIsARun i (a # p) r" by blast
          }
            
            
          {
            assume "(\<exists>node. (Cons a p) = [node])"
            hence n543 : "p = []" by auto
            def r == "[rule]"
            then have n764 : "hd r = rule" by auto
            have "pathFitsListAndListIsARun i [a] r" using a1 a2 a3 r_def pathFitsListAndListIsARun.simps by blast
            then show "\<exists>r. hd r = rule \<and> pathFitsListAndListIsARun i (a # p) r" using n764 n543 by auto
          } 
        qed
        then show "\<exists>r. hd r |\<in>| \<R> i \<and> pathFitsListAndListIsARun i (a # p) r" using n654654 by auto
      qed
    qed
  qed
  hence "\<And>\<R> x tree p. x \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i) \<Longrightarrow> tree |\<in>| x \<Longrightarrow>  p \<in>pathsInTree tree \<Longrightarrow> pathSatisfiesApproximatorForRuleSet p (\<R> i) i" by auto
  hence  "\<And>\<R> x tree. x \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i) \<Longrightarrow> tree |\<in>| x \<Longrightarrow> tree \<in> {tr. \<forall>p\<in>pathsInTree tr. pathSatisfiesApproximatorForRuleSet p (\<R> i) i}" by auto
  hence  "\<And>\<R> x tree. x \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i) \<Longrightarrow> tree \<in> (fset x) \<Longrightarrow> tree \<in> {tr. \<forall>p\<in>pathsInTree tr. pathSatisfiesApproximatorForRuleSet p (\<R> i) i}" using notin_fset
  proof -
    fix \<R> :: "ot \<Rightarrow> (stt, abc) rule fset" and x :: "abc tree fset" and tree :: "abc tree"
    assume a1: "tree \<in> fset x"
    assume a2: "x \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i)"
    assume "\<And>x \<R> tree. \<lbrakk>x \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i); tree |\<in>| x\<rbrakk> \<Longrightarrow> tree \<in> {tr. \<forall>p\<in>pathsInTree tr. pathSatisfiesApproximatorForRuleSet p (\<R> i) i}"
    then show "tree \<in> {t. \<forall>ns\<in>pathsInTree t. pathSatisfiesApproximatorForRuleSet ns (\<R> i) i}"    using a2 a1 by (meson notin_fset)
  qed 
    hence  "\<And>\<R> x . x \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i) \<Longrightarrow> (\<And> tree . tree \<in> (fset x) \<Longrightarrow> tree \<in> {tr. \<forall>p\<in>pathsInTree tr. pathSatisfiesApproximatorForRuleSet p (\<R> i) i})" by auto
  then show "\<And>\<R> x. x \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i) \<Longrightarrow> (fset x \<subseteq> {tr. \<forall>p\<in>pathsInTree tr. pathSatisfiesApproximatorForRuleSet p (\<R> i) i})" by auto
qed
  
  
  
  
  
lemma noEmptyForests0 :
  assumes "forest \<in> \<L>\<^sub>\<phi>\<^sub>\<sigma> automaton s"
  shows "forest \<noteq> {||}"
  proof -
    have "\<exists> tree . tree |\<in>| forest" using assms(1) by (simp add: forest_language_for_state_def) 
        then show ?thesis by auto
  qed
    
  
                  
lemma noEmptyForests :
  assumes "l |\<in>| (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) |`|stateset)"
  assumes "forest \<in> l"
  shows "forest \<noteq> {||}"
  using noEmptyForests0
  using assms(1) assms(2) by fastforce 

    
  
lemma singletonPathsMeansSingletonTree :
  fixes forest \<alpha>
  assumes n75478 : "\<And>tree path . tree \<in> (fset forest) \<Longrightarrow> (path |\<in>| (\<Pi> tree)) \<Longrightarrow> path = [\<alpha>]"
  shows "\<And>tree . tree \<in> (fset forest) \<Longrightarrow> tree = (NODE \<alpha> fempty)"
proof -
  fix tree
  assume n75687 :  "tree \<in> (fset forest)"
  obtain root children where n54668978 : "tree = (NODE root children)" using tree.exhaust by auto
  then have n6587 : " (\<Pi> (NODE root children)) |\<subseteq>| (finsert [\<alpha>] fempty)" using n75478  n75687          using \<ff>_def n75687 by force 
  from pathAlternateDef have n54647 : "(\<Pi> (NODE root children)) = (\<lambda> x. (root#x)) |`| (\<Union>| (\<Pi> |`| children) |\<union>| {|[]|})" by auto
  from n6587 have n656587 : "(\<Pi> (NODE root children)) |\<subseteq>| (\<lambda> x. (root#x)) |`| ({|[]|})" by auto
  have n6445877 : "(\<lambda> x. (root#x)) |`| ({|[]|}) = (finsert [root] fempty)" by simp
  hence n76535 : "(finsert [root] fempty) |\<subseteq>| (finsert [\<alpha>] fempty)" using n6587  n656587 by auto
  hence n7698 :  "root = \<alpha>" by auto
  hence " (\<lambda> x. (\<alpha>#x)) |`| (\<Union>| (\<Pi> |`| children) |\<union>| {|[]|}) |\<subseteq>| (finsert [\<alpha>] fempty)" using n76535 n6445877 n54647 n656587 by auto
  hence "(\<Union>| (\<Pi> |`| children) |\<union>| {|[]|}) = {|[]|}" by auto
  hence "(\<Union>| (\<Pi> |`| children)) |\<union>| {|[]|} = {|[]|}" by auto
  hence "(\<Union>| (\<Pi> |`| children)) |\<subseteq>| {|[]|}" by auto
  hence "\<And>path . path |\<in>| (\<Union>| (\<Pi> |`| children)) \<Longrightarrow> path = []" by auto
  hence "\<And> childrenpath path . childrenpath |\<in>| (\<Pi> |`| children) \<Longrightarrow> path |\<in>| childrenpath \<Longrightarrow> path = []" by auto
  hence "\<And> path child. child |\<in>| children \<Longrightarrow> path |\<in>| \<Pi> child \<Longrightarrow> path = []" by auto
  hence "\<And>  child. child |\<in>| children \<Longrightarrow> False" using rootIsPath2 by auto
  hence "children = fempty" by auto
  then show "tree = (NODE \<alpha> fempty)" using n7698 n54668978 by auto
qed
  
  
    
    (* ========================================================================================== *)
    
fun childrenPathsetsAreSubsets :: "abc node list \<Rightarrow> abc node list \<Rightarrow> bool" where
  "childrenPathsetsAreSubsets [] [] = True"
| "childrenPathsetsAreSubsets [] (a#b) = False"
| "childrenPathsetsAreSubsets (a#b) [] = False"
| "childrenPathsetsAreSubsets (a#b) (c#d) = ((childrenPathsetsAreSubsets b d) 
                                               \<and> ( labelOfNode a = labelOfNode c  )
                                               \<and> (\<Pi> (down a) |\<subseteq>| \<Pi> (down c))
                                                )"
  
  
lemma childrenWithSymbolIdempotent :  
  "\<And> (symbol :: abc) . ((childrenWithSymbol symbol (childrenWithSymbol symbol z)) = (childrenWithSymbol symbol z))"
proof -
  fix symbola :: abc
  obtain ff :: "abc tree fset \<Rightarrow> abc tree \<Rightarrow> abc tree fset" where
    f1: "\<forall>x0 x1. (\<exists>v2. x0 = finsert x1 v2 \<and> x1 |\<notin>| v2) = (x0 = finsert x1 (ff x0 x1) \<and> x1 |\<notin>| ff x0 x1)"
    by moura
  obtain tt :: "abc tree fset \<Rightarrow> abc tree fset \<Rightarrow> abc tree" where
    "\<forall>x0 x1. (\<exists>v2. v2 |\<in>| x1 \<and> v2 |\<notin>| x0) = (tt x0 x1 |\<in>| x1 \<and> tt x0 x1 |\<notin>| x0)"
    by moura
  then have "\<forall>f fa. tt fa f |\<in>| f \<and> tt fa f |\<notin>| fa \<or> f |\<subseteq>| fa"
    by blast
  moreover
  { assume "tt (inf_fset2 (childrenWithSymbol symbola z) {t. root t = symbola}) (inf_fset2 z {t. root t = symbola}) |\<notin>| inf_fset2 (ff z (tt (inf_fset2 (childrenWithSymbol symbola z) {t. root t = symbola}) (inf_fset2 z {t. root t = symbola}))) {t. root t = symbola}"
    moreover
    { assume "inf_fset2 (ff z (tt (inf_fset2 (childrenWithSymbol symbola z) {t. root t = symbola}) (inf_fset2 z {t. root t = symbola}))) {t. root t = symbola} \<noteq> inf_fset2 z {t. root t = symbola}"
      moreover
      { assume "z \<noteq> finsert (tt (inf_fset2 (childrenWithSymbol symbola z) {t. root t = symbola}) (inf_fset2 z {t. root t = symbola})) (ff z (tt (inf_fset2 (childrenWithSymbol symbola z) {t. root t = symbola}) (inf_fset2 z {t. root t = symbola}))) \<or> tt (inf_fset2 (childrenWithSymbol symbola z) {t. root t = symbola}) (inf_fset2 z {t. root t = symbola}) |\<in>| ff z (tt (inf_fset2 (childrenWithSymbol symbola z) {t. root t = symbola}) (inf_fset2 z {t. root t = symbola}))"
        then have "tt (inf_fset2 (childrenWithSymbol symbola z) {t. root t = symbola}) (inf_fset2 z {t. root t = symbola}) |\<notin>| inf_fset2 z {t. root t = symbola} \<or> tt (inf_fset2 (childrenWithSymbol symbola z) {t. root t = symbola}) (inf_fset2 z {t. root t = symbola}) |\<in>| inf_fset2 (childrenWithSymbol symbola z) {t. root t = symbola}"
          using f1 by (meson finterD1 set_finsert) }
      ultimately have "tt (inf_fset2 (childrenWithSymbol symbola z) {t. root t = symbola}) (inf_fset2 z {t. root t = symbola}) |\<notin>| inf_fset2 z {t. root t = symbola} \<or> tt (inf_fset2 (childrenWithSymbol symbola z) {t. root t = symbola}) (inf_fset2 z {t. root t = symbola}) |\<in>| inf_fset2 (childrenWithSymbol symbola z) {t. root t = symbola}"
        by (metis childrenWithSymbol_def finterI finter_finsert_left_ifffempty) }
    ultimately have "tt (inf_fset2 (childrenWithSymbol symbola z) {t. root t = symbola}) (inf_fset2 z {t. root t = symbola}) |\<notin>| inf_fset2 z {t. root t = symbola} \<or> tt (inf_fset2 (childrenWithSymbol symbola z) {t. root t = symbola}) (inf_fset2 z {t. root t = symbola}) |\<in>| inf_fset2 (childrenWithSymbol symbola z) {t. root t = symbola}"
      by metis }
  ultimately show "childrenWithSymbol symbola (childrenWithSymbol symbola z) = childrenWithSymbol symbola z"
    using f1 by (metis childrenWithSymbol_def finterD1 fset_eq_fsubset set_finsert)
qed
  
lemma psiPathsMonotonic :
  assumes "a |\<subseteq>| b"
  shows "pathsInForest (psiF a) |\<subseteq>| pathsInForest (psiF b)"
  by (metis (mono_tags, lifting) assms fsubsetD fsubsetI pathsTreeForest psiPreservesPaths) 
    
lemma psiTreeForestMonotonic :
  fixes a :: "abc tree"
  fixes t :: "abc tree"
  fixes symbol :: abc
  assumes "a |\<in>| (childrenWithSymbol symbol z)"
  assumes "t = psi (NODE symbol (\<Union>| (childrenSet |`| (childrenWithSymbol symbol z))))"
  shows "\<delta>\<^sub>\<tau> a |\<subseteq>| \<delta>\<^sub>\<tau> t"
proof -
  have "(finsert a fempty) |\<subseteq>| (childrenWithSymbol symbol z)" using assms(1)    by simp 
  have "pathsInForest (finsert a fempty) = \<delta>\<^sub>\<tau> a"    by (simp add: pathsSingeton) 
  have a1 : "root |`| (childrenWithSymbol symbol z) = (finsert symbol fempty)" 
  proof (simp add : childrenWithSymbol_def)
    show "root |`| inf_fset2 z {child1. root child1 = symbol} = {|symbol|}"
    proof
      show " root |`| inf_fset2 z {child1. root child1 = symbol} |\<subseteq>| {|symbol|}"
        by (metis (mono_tags, lifting) Int_iff fimage_fsubsetI finsertCI inf_fset2.rep_eq mem_Collect_eq notin_fset) 
      show "{|symbol|} |\<subseteq>| root |`| inf_fset2 z {child1. root child1 = symbol} " using assms(1)
        by (metis Collect_cong \<open>root |`| inf_fset2 z {child1. root child1 = symbol} |\<subseteq>| {|symbol|}\<close> childrenWithSymbol_def fempty_is_fimage finsert_not_fempty fsubset_fsingletonD mk_disjoint_finsert) 
    qed
  qed
  have "(finsert t fempty) = psiF (childrenWithSymbol symbol z)" 
  proof (simp add : psiF_def  assms(2))
    have "((\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 (childrenWithSymbol symbol z))))) \<circ> root) |`| childrenWithSymbol symbol z =
((\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 (childrenWithSymbol symbol z))))) |`| (root) |`| childrenWithSymbol symbol z)" by auto 
    hence "((\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 (childrenWithSymbol symbol z))))) \<circ> root) |`| childrenWithSymbol symbol z =
((\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 (childrenWithSymbol symbol z))))) |`| (finsert symbol fempty))" using a1 by auto
    have "((\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 (childrenWithSymbol symbol z))))) |`| (finsert symbol fempty))
          = {|psi (NODE symbol (\<Union>| (childrenSet |`| childrenWithSymbol symbol z)))|}" using childrenWithSymbolIdempotent by auto
    then show "{|psi (NODE symbol (\<Union>| (childrenSet |`| childrenWithSymbol symbol z)))|} =
    ((\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 (childrenWithSymbol symbol z))))) \<circ> root) |`| childrenWithSymbol symbol z" using a1
      by (simp add: \<open>((\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 (childrenWithSymbol symbol z))))) \<circ> root) |`| childrenWithSymbol symbol z = (\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 (childrenWithSymbol symbol z))))) |`| {|symbol|}\<close>) 
  qed
  have "pathsInForest (finsert t fempty) = \<delta>\<^sub>\<tau> t" by (simp add: pathsSingeton) 
  show "\<delta>\<^sub>\<tau> a |\<subseteq>| \<delta>\<^sub>\<tau> t " using psiPathsMonotonic
    using \<open>\<Pi>\<^sub>\<iota>\<^sub>\<phi> {|a|} = \<delta>\<^sub>\<tau> a\<close> \<open>\<Pi>\<^sub>\<iota>\<^sub>\<phi> {|t|} = \<delta>\<^sub>\<tau> t\<close> \<open>{|a|} |\<subseteq>| childrenWithSymbol symbol z\<close> \<open>{|t|} = \<Psi>\<^sub>\<phi> (childrenWithSymbol symbol z)\<close> psiPreservesPaths by auto 
qed
  
    
  
  
  
lemma psiSubsetsLemma2 :
  fixes p
  shows "\<And> t x z . t |\<in>| x \<Longrightarrow> p \<in> (pathsInTree t) \<Longrightarrow> x = psiF z \<Longrightarrow> (\<exists>t2 p2.(t2 |\<in>| z \<and> childrenPathsetsAreSubsets p2 p \<and> p2 \<in> pathsInTree t2))"
proof (induct p)
  case Nil
  hence "False" using  noEmptyPaths pathsInTree_def   by (simp add: pathsInTree_def) 
  then show ?case by auto
next
  case (Cons a p)
  from Cons.prems(2) have a1 : "(isAPathp (a # p))" using pathsInTree_def by blast
  from Cons.prems(2) have n654654 : "(( down a = t))" using pathsInTree_def by blast
  have n14558 : "p = [] \<Longrightarrow> (\<exists> witnessTree . witnessTree |\<in>| z \<and> root witnessTree = root t \<and> \<delta>\<^sub>\<tau> witnessTree |\<subseteq>| \<delta>\<^sub>\<tau> t)"
  proof -
    assume "p = []"
    have nu674543 : "down a |\<in>| psiF z" using Cons.prems(1)    Cons.prems(3) n654654 by auto
    from psiF_def have n865654 : "psiF z = (\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 z)))) |`| root |`| z " by auto
    then obtain symbol where n76454 : "down a = psi (NODE symbol (\<Union>| (childrenSet |`| childrenWithSymbol symbol z)))" and "symbol |\<in>| (root |`| z)" using nu674543 by auto
    then obtain witnessTree where n864653 : "witnessTree |\<in>| z" and n864543 : "root witnessTree = symbol" by auto
    hence n875653 : "witnessTree |\<in>| childrenWithSymbol symbol z" using childrenWithSymbol_def   by (simp add: childrenWithSymbol_def finterI) 
    from n654654  n864543 n76454 root.simps  have "(root witnessTree = root t)"      by (simp add: n654654 psiRoot) 
    have "t = psi (NODE symbol (\<Union>| (childrenSet |`| childrenWithSymbol symbol z)))" using n76454 n654654 by auto
    have "\<delta>\<^sub>\<tau> witnessTree |\<subseteq>| \<delta>\<^sub>\<tau> t" using psiTreeForestMonotonic
      using \<open>t = psi (NODE symbol (\<Union>| (childrenSet |`| childrenWithSymbol symbol z)))\<close> n875653 by blast 
    have "witnessTree |\<in>| z \<and> root witnessTree = root t \<and> \<delta>\<^sub>\<tau> witnessTree |\<subseteq>| \<delta>\<^sub>\<tau> t"
      by (simp add: \<open>\<delta>\<^sub>\<tau> witnessTree |\<subseteq>| \<delta>\<^sub>\<tau> t\<close> \<open>root witnessTree = root t\<close> n864653) 
    then show "(\<exists> witnessTree . witnessTree |\<in>| z \<and> root witnessTree = root t \<and> \<delta>\<^sub>\<tau> witnessTree |\<subseteq>| \<delta>\<^sub>\<tau> t)" by auto
  qed
  from a1 isAPath.simps isAPathp_isAPath_eq have "((\<exists>node. (a # p) = [node]) \<or> (\<exists>path e2. (a # p) = e2 # path \<and> path \<in> isAPath \<and> (\<exists>e1 tail. path = e1 # tail \<and> immediatelyDominates e2 e1)))"  by metis
  hence "p = [] \<or> ( (p \<in> isAPath \<and> (\<exists>e1 tail. p = e1 # tail \<and> immediatelyDominates a e1)))" by blast
  hence "p = [] \<or> ( (p \<in> isAPath \<and> (\<exists>e1 tail. p = e1 # tail \<and>  ((down e1) |\<in>| (childrenSet (down a))) )))" using immediatelyDominates_def by auto
  then obtain e1 tail where "p \<noteq> [] \<Longrightarrow> ( p = e1 # tail \<and> ((down e1) |\<in>| (childrenSet (down a))))" by auto
  hence ny54r654 : "p \<noteq> [] \<Longrightarrow> ( p = e1 # tail \<and> ((down e1) |\<in>| (childrenSet t)))" using n654654 by auto
  from Cons.prems(3) psiF_def have "x = (\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 z)))) |`| root |`| z " by auto
  hence n65464 : "x = (\<lambda>symbol2.  (NODE symbol2 (psiF (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 z))))) |`| root |`| z " using psiDef psiF_def    by (smt fset.map_cong0) 
  from Cons.prems(1) n65464 obtain tree where n76798798 : "t = (NODE (root tree) (psiF (\<Union>| (childrenSet |`| childrenWithSymbol (root tree) z))))" by auto
  hence n54564 : "childrenSet t = ((psiF (\<Union>| (childrenSet |`| childrenWithSymbol (root tree) z))))" by simp
  hence "p \<noteq> [] \<Longrightarrow> (down e1) |\<in>| ((psiF (\<Union>| (childrenSet |`| childrenWithSymbol (root tree) z))))" using ny54r654 n54564 by auto
  def downT == "(down e1)"
  def downX == "childrenSet t"
  def downZ == "(\<Union>| (childrenSet |`| childrenWithSymbol (root tree) z))"
  have a1 : "p \<noteq> [] \<Longrightarrow> downT |\<in>| downX"
    using downT_def downX_def ny54r654 by auto 
  have a2 : "p \<noteq> [] \<Longrightarrow> p \<in> pathsInTree downT"
    by (smt Cons.prems(2) downT_def isAPathp.simps list.sel(3) mem_Collect_eq ny54r654 pathsInTree_def) 
  have a3 : "p \<noteq> [] \<Longrightarrow> downX = \<Psi>\<^sub>\<phi> downZ"
    by (simp add: downX_def downZ_def n54564) 
  from a1 a2 a3 Cons.hyps obtain t2 p2 where n76565 : "p \<noteq> [] \<Longrightarrow> (t2 |\<in>| downZ \<and> childrenPathsetsAreSubsets p2 p \<and> p2 \<in> pathsInTree t2)" and ny54543 : "p = [] \<Longrightarrow> p2 = []"  by meson 
  hence n65654654 :  "p \<noteq> [] \<Longrightarrow> p2 \<in> pathsInTree t2" by auto
  hence n6576 : "p \<noteq> [] \<Longrightarrow> p2 \<noteq>[] \<Longrightarrow> p2 \<in> isAPath" using pathsInTree_def isAPath.simps isAPathp_isAPath_eq
  proof -
    assume "p \<noteq> []"
    then have "isAPathp p2"
      using n65654654 pathsInTree_def by fastforce
    then show ?thesis
      by (metis (lifting) isAPathp_isAPath_eq)
  qed 
  from n65654654 pathsInTree_def have ny5543 : "p \<noteq> [] \<Longrightarrow> (\<exists>e1 tail. p2 = e1 # tail \<and> down e1 = t2)" by auto
  from downZ_def n76565 n14558 obtain elementOfZ where n65463 : "p \<noteq> [] \<Longrightarrow> t2 |\<in>| childrenSet elementOfZ" and n6545876 : "p \<noteq> [] \<Longrightarrow> elementOfZ |\<in>|  childrenWithSymbol (root tree) z" 
    and n47885787 : "p = [] \<Longrightarrow>( elementOfZ |\<in>| z \<and> root elementOfZ = root t \<and> \<delta>\<^sub>\<tau> elementOfZ |\<subseteq>| \<delta>\<^sub>\<tau> t)"    using Cons.prems(1) \<open>x = (\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 z)))) |`| root |`| z\<close> by auto 
  hence ny654653 : " p \<noteq> [] \<Longrightarrow> elementOfZ |\<in>| z" using childrenWithSymbol_def    by (metis finterD1)
  def newT2 == "elementOfZ"
  obtain newNode where nu65654 : "down (newNode :: abc node) = elementOfZ"  using nodeExists by auto
  def newP2 == "newNode#p2"
  from newT2_def ny654653 n47885787 have "newT2 |\<in>| z" by auto
  have "childrenPathsetsAreSubsets newP2 (Cons a p)"
  proof (simp add : newP2_def)
    show "childrenPathsetsAreSubsets p2 p \<and> labelOfNode newNode = labelOfNode a \<and> \<delta>\<^sub>\<tau> (down newNode) |\<subseteq>| \<delta>\<^sub>\<tau> (down a)"
    proof
      from n76565 show "childrenPathsetsAreSubsets p2 p" using ny54543 childrenPathsetsAreSubsets.simps(1) by metis
      show " labelOfNode newNode = labelOfNode a \<and> \<delta>\<^sub>\<tau> (down newNode) |\<subseteq>| \<delta>\<^sub>\<tau> (down a) " 
      proof (simp add : labelOfNode_def nu65654 n654654)
        from n6545876 have ny765876 : "p \<noteq> [] \<Longrightarrow> elementOfZ |\<in>|  childrenWithSymbol (root tree) z" by auto
        from n76798798 have "t = (NODE (root tree) (psiF (\<Union>| (childrenSet |`| childrenWithSymbol (root tree) z))))" by auto
        hence a1 : "root tree = root t" by auto
        from ny765876 childrenWithSymbol_def have a2 : "p \<noteq> [] \<Longrightarrow> root elementOfZ = root tree" 
        proof (simp add :childrenWithSymbol_def)
          show "p \<noteq> [] \<Longrightarrow> elementOfZ |\<in>| inf_fset2 z {child1. root child1 = root tree} \<Longrightarrow> root elementOfZ = root tree"
            by (metis IntD2 inf_fset2.rep_eq mem_Collect_eq notin_fset)
        qed
        from a1 a2 have n76987 : "p \<noteq> [] \<Longrightarrow> root elementOfZ = root t" by auto
        from ny765876   have "p \<noteq> [] \<Longrightarrow>  \<delta>\<^sub>\<tau> elementOfZ |\<subseteq>| pathsInForest (childrenWithSymbol (root tree) z)" using pathsInForest_def by auto
        from n76798798  have "t = (NODE (root tree) (psiF (\<Union>| (childrenSet |`| childrenWithSymbol (root tree) z))))" by auto
        hence "\<delta>\<^sub>\<tau> t = fimage (\<lambda> tail.((root tree)#tail)) ((\<Union>| (fimage \<Pi> (psiF (\<Union>| (childrenSet |`| childrenWithSymbol (root tree) z))))) |\<union>|  (finsert [] {||}))" using pathAlternateDef by auto
        hence "\<delta>\<^sub>\<tau> t = fimage (\<lambda> tail.((root tree)#tail)) (pathsInForest ( ((((psiF (\<Union>| (childrenSet |`| childrenWithSymbol (root tree) z))))))) |\<union>|  (finsert [] {||}))" using pathsInForest_def by auto
        hence n76798 : "\<delta>\<^sub>\<tau> t = fimage (\<lambda> tail.((root tree)#tail)) (pathsInForest (\<Union>| (childrenSet |`| childrenWithSymbol (root tree) z)) |\<union>|  (finsert [] {||}))" using psiPreservesPaths by auto
        obtain rootE childrenE where ny56ty8 : "elementOfZ = (NODE rootE childrenE)"          using tree.exhaust by auto 
        hence ny687 : "\<delta>\<^sub>\<tau> elementOfZ = fimage (\<lambda> tail.((rootE)#tail)) (((\<Union>| (fimage \<Pi> childrenE)) |\<union>|  (finsert [] {||})))" using pathAlternateDef by auto
        from n76987  ny56ty8 have "p \<noteq> [] \<Longrightarrow> rootE = root tree" using root.simps          using a1 by auto 
        hence "p \<noteq> [] \<Longrightarrow> \<delta>\<^sub>\<tau> elementOfZ = fimage (\<lambda> tail.((root tree)#tail)) (((\<Union>| (fimage \<Pi> childrenE)) |\<union>|  (finsert [] {||})))"  using ny687 by auto
        hence n54576 : "p \<noteq> [] \<Longrightarrow> \<delta>\<^sub>\<tau> elementOfZ = fimage (\<lambda> tail.((root tree)#tail)) ((pathsInForest (( childrenE))) |\<union>|  (finsert [] {||}))"  using pathsInForest_def by auto
        have ny568767 : "childrenE = childrenSet elementOfZ" using ny56ty8          by simp 
        have "p \<noteq> [] \<Longrightarrow> elementOfZ |\<in>| childrenWithSymbol (root tree) z"          by (simp add: ny765876) 
        hence "p \<noteq> [] \<Longrightarrow>  childrenE |\<subseteq>| \<Union>| (childrenSet |`| childrenWithSymbol (root tree) z)" using ny568767          by (simp add: ffUnion_upper) 
        hence "p \<noteq> [] \<Longrightarrow>  ((pathsInForest (( childrenE))) |\<subseteq>| (pathsInForest (\<Union>| (childrenSet |`| childrenWithSymbol (root tree) z))))"          by (simp add: fimage_mono pathsInForest_def) 
        hence "p \<noteq> [] \<Longrightarrow>((pathsInForest (( childrenE))) |\<union>|  (finsert [] {||})) |\<subseteq>| (pathsInForest (\<Union>| (childrenSet |`| childrenWithSymbol (root tree) z)) |\<union>|  (finsert [] {||}))"         by auto 
        hence "p \<noteq> [] \<Longrightarrow> \<delta>\<^sub>\<tau> elementOfZ  |\<subseteq>| \<delta>\<^sub>\<tau> t" using n76798 n54576 by auto
        have "pathsInForest (childrenWithSymbol (root tree) z) = \<Union>| (\<Pi> |`| (childrenWithSymbol (root tree) z))" using pathsInForest_def by auto
        have "\<And> root children . \<Pi> (NODE root children) = fimage (\<lambda> tail.((root)#tail)) ((\<Union>| (fimage \<Pi> children))|\<union>| {|[]|})" using pathAlternateDef by auto
        have "p \<noteq> [] \<Longrightarrow> (root elementOfZ = root t \<and> \<delta>\<^sub>\<tau> elementOfZ |\<subseteq>| \<delta>\<^sub>\<tau> t)"
          by (simp add: \<open>p \<noteq> [] \<Longrightarrow> \<delta>\<^sub>\<tau> elementOfZ |\<subseteq>| \<delta>\<^sub>\<tau> t\<close> n76987) 
        then show "(root elementOfZ = root t \<and> \<delta>\<^sub>\<tau> elementOfZ |\<subseteq>| \<delta>\<^sub>\<tau> t)" using n47885787 by auto
      qed
    qed
  qed
  have "newP2 \<in> pathsInTree newT2"
  proof (simp add : pathsInTree_def isAPathp_isAPath_eq  )
    from nu65654 n65463 have nt43543 : "p \<noteq> [] \<Longrightarrow> t2 |\<in>| (childrenSet (down newNode))" by auto
    hence "p \<noteq> [] \<Longrightarrow> ((p2 = []) \<or> ((\<exists>e1 tail. p2 = e1 # tail \<and> (down e1) |\<in>| (childrenSet (down newNode))) ))" using ny5543 by auto
    hence "((p2 = []) \<or> ((\<exists>e1 tail. p2 = e1 # tail \<and> (down e1) |\<in>| (childrenSet (down newNode))) ))" using ny54543 by auto
    hence " ((p2 = []) \<or> ((\<exists>e1 tail. p2 = e1 # tail \<and> immediatelyDominates newNode e1)))" using immediatelyDominates_def by auto
    hence " ((p2 = []) \<or> (p2 \<in> isAPath \<and> (\<exists>e1 tail. p2 = e1 # tail \<and> immediatelyDominates newNode e1)))" using n6576  using \<open>childrenPathsetsAreSubsets newP2 (a # p)\<close> childrenPathsetsAreSubsets.simps(3) childrenPathsetsAreSubsets.simps(4) newP2_def by blast 
    hence " ((p2 = []) \<or> (\<exists>path e2. newNode#p2 = e2 # path \<and> p2 \<in> isAPath \<and> (\<exists>e1 tail. p2 = e1 # tail \<and> immediatelyDominates newNode e1)))" by auto
    hence " ((p2 = []) \<or> (\<exists>path e2. newNode#p2 = e2 # path \<and> path \<in> isAPath \<and> (\<exists>e1 tail. path = e1 # tail \<and> immediatelyDominates e2 e1)))" by auto
    hence " ((\<exists>node. newNode#p2 = [node]) \<or> (\<exists>path e2. newNode#p2 = e2 # path \<and> path \<in> isAPath \<and> (\<exists>e1 tail. path = e1 # tail \<and> immediatelyDominates e2 e1)))" by auto
    hence " ((\<exists>node. newP2 = [node]) \<or> (\<exists>path e2. newP2 = e2 # path \<and> path \<in> isAPath \<and> (\<exists>e1 tail. path = e1 # tail \<and> immediatelyDominates e2 e1)))" by (simp add :newP2_def)
    hence n6546767 : " newP2 \<in> isAPath" using isAPath.simps by metis
    from newP2_def newT2_def nu65654 have "((newP2 = newNode#p2) \<and> down newNode = newT2)" by auto
    hence n5476678 : "(\<exists>e1. (\<exists>tail. newP2 = e1 # tail) \<and> down e1 = newT2)" by auto
    from n6546767 n5476678 show "newP2 \<in> isAPath \<and> (\<exists>e1. (\<exists>tail. newP2 = e1 # tail) \<and> down e1 = newT2)" by auto
  qed
  def child == "down e1"
  have "t |\<in>| x \<Longrightarrow> p \<in> pathsInTree t \<Longrightarrow> x = \<Psi>\<^sub>\<phi> z \<Longrightarrow> \<exists>t2 p2. t2 |\<in>| z \<and> childrenPathsetsAreSubsets p2 p \<and> p2 \<in> pathsInTree t2"
    using Cons.hyps by blast
  then show ?case
    using \<open>childrenPathsetsAreSubsets newP2 (a # p)\<close> \<open>newP2 \<in> pathsInTree newT2\<close> \<open>newT2 |\<in>| z\<close> by auto 
qed
  
  
    
  
  (* =================================================== *)
  
  (* In this section, the goal is to show g \<subseteq> f  *)
  
lemma subsetsRunsLemma :
  fixes \<ii> p2 
  shows "\<And> r p. childrenPathsetsAreSubsets p2 p \<Longrightarrow> (pathFitsListAndListIsARun \<ii> p2 r) \<Longrightarrow>pathFitsListAndListIsARun \<ii> p r"
proof (induct p2)
  case Nil
  assume "childrenPathsetsAreSubsets [] p"
  then have a1 : "p = []" using list.exhaust    using childrenPathsetsAreSubsets.elims(2) by auto  
  assume "pathFitsListAndListIsARun \<ii> [] r"
  then have a2 : "r = []" using pathFitsListAndListIsARun.simps by (metis list.exhaust)       
  then show ?case using a1 a2 by simp
next
  case (Cons a p2)
  assume b1 : "\<And> r p.(childrenPathsetsAreSubsets p2 p \<Longrightarrow> pathFitsListAndListIsARun \<ii> p2 r \<Longrightarrow> pathFitsListAndListIsARun \<ii> p r)"
  assume b2 : "childrenPathsetsAreSubsets (a # p2) p"
  assume b3 : "pathFitsListAndListIsARun \<ii> (a # p2) r"
    
    
  have y1 : "r = (hd r)#(tl r)"
    by (metis b3 list.exhaust_sel nonMatching) 
  have "p = (hd p)#(tl p)" using b2
    using childrenPathsetsAreSubsets.simps(3) list.exhaust_sel by blast 
      
  from b2 have c1 : "childrenPathsetsAreSubsets  p2 (tl p)"
    by (metis \<open>p = hd p # tl p\<close> childrenPathsetsAreSubsets.simps(4)) 
  from b3 have c2 : "pathFitsListAndListIsARun \<ii> p2 (tl r)"
    by (metis \<open>r = hd r # tl r\<close> pathFitsListAndListIsARun.simps(2)) 
  from b1 c1 c2 have "pathFitsListAndListIsARun \<ii> (tl p) (tl r)" by auto
  from b3 pathFitsListAndListIsARun.simps have "(labelOfNode a = symbol (hd r))" by (metis hd_Cons_tl) 
  from b3 pathFitsListAndListIsARun.simps have "((hd r) |\<in>| rule_set (\<A> \<ii>))" by (metis hd_Cons_tl)
  from b3 pathFitsListAndListIsARun.simps   have " (( (down a)) \<in> ( \<V>\<^sub>\<tau> \<ii> (hd r)  )   )" by (metis hd_Cons_tl)
  from b3 pathFitsListAndListIsARun.simps   have " (pathFitsListAndListIsARun \<ii> p2 (tl r))" by (metis hd_Cons_tl)
  from b3 pathFitsListAndListIsARun.simps   have " (\<forall> h.\<forall> t.((tl r) = (h#t) \<longrightarrow>  (        (((transition (\<A> \<ii>) (states h) (symbol h) )  |\<in>| states (hd r)) )        )))" by (metis hd_Cons_tl)
  from b2 have u1 :  "( labelOfNode a = labelOfNode (hd p)  )
                                               \<and> (\<Pi> (down a) |\<subseteq>| \<Pi> (down (hd p)))
                                                "
    by (metis \<open>p = hd p # tl p\<close> childrenPathsetsAreSubsets.simps(4)) 
  have "(labelOfNode (hd p) = symbol (hd r))"
    using \<open>labelOfNode a = labelOfNode (hd p) \<and> \<delta>\<^sub>\<tau> (down a) |\<subseteq>| \<delta>\<^sub>\<tau> (down (hd p))\<close> \<open>labelOfNode a = symbol (hd r)\<close> by auto 
      
  have " (( (down (hd p))) \<in> ( \<V>\<^sub>\<tau> \<ii> (hd r)  )   )"
  proof -
    have " (( (down a)) \<in> ( \<V>\<^sub>\<tau> \<ii> (hd r)  )   )"
      by (simp add: \<open>down a \<in> \<V>\<^sub>\<tau> \<ii> (hd r)\<close>)
        
    then have u2 : "(root (( (down a))) = (symbol (hd r))) \<and> \<Pi> (( (down a))) \<in> ((upwardClosure (image \<Pi> (((Z \<N> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) (hd r))))))) 
                                 \<union> (image \<Pi> {t . height t > \<N>})) 
                              \<inter> (\<Inter>I \<in> (necess (\<A> \<ii>) \<I> (hd r)) . (image \<Pi> (existential_satisfaction_set I)   ))"
      using \<V>\<^sub>\<tau>_def by blast
    then have v1 : "(root (( (down (hd p)))) = (symbol (hd r)))"
      by (metis \<open>labelOfNode (hd p) = symbol (hd r)\<close> labelOfNode_def)
    from u1 have u3 : "(\<Pi> (down a) |\<subseteq>| \<Pi> (down (hd p)))" by auto
    then show " (( (down (hd p))) \<in> ( \<V>\<^sub>\<tau> \<ii> (hd r)  )   )" using vUpwardsClosedLemma v1
      by (metis (mono_tags, lifting) \<V>\<^sub>\<tau>_def mem_Collect_eq u2)
  qed
  have " (pathFitsListAndListIsARun \<ii> (tl p) (tl r))"
    by (simp add: \<open>pathFitsListAndListIsARun \<ii> (tl p) (tl r)\<close>) 
  then show "pathFitsListAndListIsARun \<ii> p r" using pathFitsListAndListIsARun.simps
    by (metis \<open>\<forall>h t. tl r = h # t \<longrightarrow> transition (\<A> \<ii>) (states h) (symbol h) |\<in>| states (hd r)\<close> \<open>down (hd p) \<in> \<V>\<^sub>\<tau> \<ii> (hd r)\<close> \<open>hd r |\<in>| rule_set (\<A> \<ii>)\<close> \<open>labelOfNode (hd p) = symbol (hd r)\<close> \<open>p = hd p # tl p\<close> \<open>r = hd r # tl r\<close>) 
qed
  
lemma subsetsApproxPathsLemma:
  fixes \<ii> p2 p \<R>
  shows "childrenPathsetsAreSubsets p2 p \<Longrightarrow> pathSatisfiesApproximatorForRuleSet p2 (\<R> \<ii>) \<ii> \<Longrightarrow> pathSatisfiesApproximatorForRuleSet p (\<R> \<ii>) \<ii>"
proof -
  assume a2 : "childrenPathsetsAreSubsets p2 p"
  assume a3 : " pathSatisfiesApproximatorForRuleSet p2 (\<R> \<ii>) \<ii>"
  from a3 pathSatisfiesApproximatorForRuleSet_def obtain r where a10 : "((hd r |\<in>| (\<R> \<ii>)) \<and>
                      (pathFitsListAndListIsARun \<ii> p2 r))" by blast
  then have "pathFitsListAndListIsARun \<ii> p r" using subsetsRunsLemma a2 by auto
  then show "pathSatisfiesApproximatorForRuleSet p (\<R> \<ii>) \<ii>" using pathSatisfiesApproximatorForRuleSet_def a10 by blast
qed
  
  
  
  
(*lemma psiAndApproxGeneral :
  fixes \<ii> x p
  assumes "f \<in> (\<P>\<^sub>1 \<R> \<ii>)"
  shows "psi f \<in> (\<P>\<^sub>1 \<R> \<ii>)"
proof -
  from assms satisfiesApproximatorForRuleSet_def \<P>\<^sub>1_def have a2 : "(\<And> p . p \<in> (pathsInTree f) \<Longrightarrow>
             pathSatisfiesApproximatorForRuleSet p (\<R> \<ii>) \<ii>)" by blast
  have "(\<And> p . p \<in> (pathsInTree (psi f)) \<Longrightarrow>
             pathSatisfiesApproximatorForRuleSet p (\<R> \<ii>) \<ii>)"
  proof -
    fix p
    assume a1 : "p \<in> (pathsInTree (psi f))"
    from psiSubsetsLemma a1 obtain p2 where a4 : "childrenPathsetsAreSubsets p2 p \<and> p2 \<in> pathsInTree f" by blast
    from a4 a2 subsetsApproxPathsLemma show "pathSatisfiesApproximatorForRuleSet p (\<R> \<ii>) \<ii>" by auto
  qed
  then show "psi f \<in> (\<P>\<^sub>1 \<R> \<ii>)" using satisfiesApproximatorForRuleSet_def \<P>\<^sub>1_def by blast
qed*)
  
  
  
    
  
  
lemma gInF : 
  fixes \<R> :: "ot \<Rightarrow> (stt,abc) rule fset"
  fixes n
    assumes "\<And> \<R>  r i. (r |\<in>| \<R> i \<Longrightarrow> (r |\<in>| rule_set (\<A> i)))"
  shows "\<Union>| (\<Z>\<^sub>\<phi> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (((\<R>) \<aa>\<^sub>1))((((\<R>) \<aa>\<^sub>2))))) |\<subseteq>| (\<ff> n  \<R>)"

proof
  fix x
  assume b0 : "x |\<in>| \<Union>| (\<Z>\<^sub>\<phi> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (((\<R>) \<aa>\<^sub>1))((((\<R>) \<aa>\<^sub>2)))))"
  from b0 obtain y where b1 : "x |\<in>| y" and b2 : "y |\<in>|  (\<Z>\<^sub>\<phi> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (((\<R>) \<aa>\<^sub>1))((((\<R>) \<aa>\<^sub>2)))))" by (meson ffUnionLemma)
  from b2 have b3 : "heightForestBounded y n" using \<Z>\<^sub>\<phi>_def heightForestBounded_def by (metis (mono_tags, lifting) finterD1 mem_Collect_eq notin_fset restrictionIsFiniteForests) 
from b2 have  b4 : "y \<in> (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (((\<R>) \<aa>\<^sub>1))((((\<R>) \<aa>\<^sub>2))))" using \<Z>\<^sub>\<phi>_def  by (metis (no_types, lifting) IntD2 inf_fset2.rep_eq notin_fset)
  from \<Psi>\<^sub>\<Sigma>\<^sub>\<rho>_def b4 
  have b6 : "y \<in> (\<Psi>\<^sub>\<phi> ` ((\<Uplus> ( ((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| (((\<R>) \<aa>\<^sub>1)))))))
                       \<inter> (\<Psi>\<^sub>\<phi> ` ((\<Uplus> ( ((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>2) |`| (((\<R>) \<aa>\<^sub>2)))))))" by metis                      
  from aut_def b6 have c10 : "\<And> \<ii>. y \<in> (\<Psi>\<^sub>\<phi> ` ((\<Uplus> ( ((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>)) |`| (((\<R>) \<ii>)))))))" by (metis (full_types) IntE \<A>.cases)
  have "\<And>i . fset y \<subseteq> (\<P>\<^sub>1 \<R> i)"
  proof -
    fix i
    from c10 obtain originalForest where niu64534 : "originalForest \<in> (\<Uplus> ( ((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i)) |`| (((\<R>) i)))))" and n6587 : "y = \<Psi>\<^sub>\<phi> originalForest" by blast
    from gInFPre niu64534 assms have n754654 : "fset originalForest \<subseteq> (\<P>\<^sub>1 \<R> i)" by auto
    have "fset (\<Psi>\<^sub>\<phi> originalForest) \<subseteq> (\<P>\<^sub>1 \<R> i)"
    proof (simp add : \<P>\<^sub>1_def satisfiesApproximatorForRuleSet_def)
      have "\<And>tree . tree |\<in>| (\<Psi>\<^sub>\<phi> originalForest) \<Longrightarrow> (\<And> p. p \<in>pathsInTree tree \<Longrightarrow> pathSatisfiesApproximatorForRuleSet p (\<R> i) i)"
      proof -
        fix tree
        assume n1 : "tree |\<in>| (\<Psi>\<^sub>\<phi> originalForest)"
        fix p
        assume n2 : "p \<in>pathsInTree tree"
        from n1 n2 psiSubsetsLemma2 obtain t2 p2 where n3 : "((t2 |\<in>| originalForest \<and> childrenPathsetsAreSubsets p2 p \<and> p2 \<in> pathsInTree t2))" by blast
        from n3 n754654 have n5346 : "t2 \<in> (\<P>\<^sub>1 \<R> i)" using notin_fset by fastforce
        from n5346 \<P>\<^sub>1_def satisfiesApproximatorForRuleSet_def n3 show "pathSatisfiesApproximatorForRuleSet p (\<R> i) i"     using subsetsApproxPathsLemma by auto 
      qed
      hence "\<And>tree . tree \<in> fset (\<Psi>\<^sub>\<phi> originalForest) \<Longrightarrow> (\<forall>p\<in>pathsInTree tree. pathSatisfiesApproximatorForRuleSet p (\<R> i) i)" using notin_fset by metis
      then show "fset (\<Psi>\<^sub>\<phi> originalForest) \<subseteq> {tr. \<forall>p\<in>pathsInTree tr. pathSatisfiesApproximatorForRuleSet p (\<R> i) i}" by auto
    qed                    
    then show "fset y \<subseteq> (\<P>\<^sub>1 \<R> i)" using n6587 by auto
  qed
  hence "\<And>i . x \<in> (\<P>\<^sub>1 \<R> i)" using b1 notin_fset by fastforce
  hence n654e76 : "x \<in> \<P> \<R>" using \<P>\<^sub>1_def \<P>_def by blast
      
  from b2 b1 \<Z>\<^sub>\<phi>_def restrictionIsFiniteForests have "height x \<le> n"    using b3 heightForestBounded_def by auto 
  then show "x |\<in>| (\<ff> n  \<R>)" using \<ff>_def \<Z>\<^sub>\<tau>_def restrictionIsFinite restrictionIsFinite2 notin_fset n654e76        by (simp add: finterI) 
qed
  
      
  
  
    (* ========================================================================================== *)
lemma langRuleToState:
  fixes rule :: "(stt,abc) rule"
  assumes   "  state = transition (\<A> i) (states rule) (symbol rule)"
  assumes " x \<in> \<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) rule" 
  shows "x \<in> \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) state"
proof (simp add: forest_language_for_state_def)
  show "(\<forall>tree. tree |\<in>| x \<longrightarrow> evaluation (\<A> i) tree = state) \<and> (\<exists>tree. tree |\<in>| x)"
  proof
    show  "\<forall> tree.(tree|\<in>|x \<longrightarrow> evaluation (\<A> i) tree = state)"
    proof 
      fix tree
      show "tree|\<in>|x \<longrightarrow> evaluation (\<A> i) tree = state"
      proof
        assume "tree|\<in>|x"
        then have "tree_for_rule (\<A> i) rule tree" using  forest_language_for_rule_def assms(2) by auto
        then have "((root tree = symbol rule) \<and> ((fimage (((evaluation (\<A> i)))) (childrenSet tree)) = states rule))" using tree_for_rule_def by metis
        then   have n768 : "(fimage (evaluation (\<A> i)) (childrenSet tree)) = (states rule)" and ny568 : "(root tree = symbol rule)" by auto
        show "evaluation (\<A> i) tree = state" 
        proof (simp add: evaluation_def) 
          have "(((transition (\<A> i)) (fimage (evaluation (\<A> i)) (childrenSet tree))) ( symbol rule)) = state" using n768 assms(1) by auto
          then  have "(((transition (\<A> i)) (fimage (evaluation (\<A> i)) (childrenSet tree))) ( symbol rule)) = state" using n768 assms(1) by auto
          then  have "(((transition (\<A> i)) (fimage (evaluation (\<A> i)) (childrenSet tree))) ( root tree)) = state" using n768 assms(1)ny568 by auto
          then show "rec_tree (\<lambda>symbol1 fset2 automaton. transition automaton ((\<lambda>uu. \<pi>\<^sup>2 uu automaton) |`| fset2) symbol1) tree (\<A> i) = state" using   childrenSet.elims root.elims evaluation_def by (metis evaluation.simps root.simps)
        qed
      qed
    qed
    show "(\<exists> tree. tree |\<in>| x)" using forest_language_for_rule_def assms(2) by auto
  qed
qed
  
  
    
      
lemma psiRulesStatesLemma21 :
  assumes allRulesAreInRuleSet : "\<And>rule . rule |\<in>| rule_set (\<A> i)"
  shows "  (\<Uplus> ((\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i)) |`|  (stateSetFromRuleSet (\<W> n k \<R> i)))) = (\<Uplus> ((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i)) |`| ((\<Union>| (rulesForState i |`| (stateSetFromRuleSet (\<W> n k \<R> i))))))) "
proof
  show "\<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) |`| stateSetFromRuleSet (\<W> n k \<R> i)) \<subseteq> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<Union>| (rulesForState i |`| stateSetFromRuleSet (\<W> n k \<R> i)))"
  proof 
    fix x
    assume n798 : "x \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) |`| stateSetFromRuleSet (\<W> n k \<R> i))"
      
      
    have "(\<And>tr . tr |\<in>| x \<Longrightarrow> (\<exists> lang . lang |\<in>| (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<Union>| (rulesForState i |`| stateSetFromRuleSet (\<W> n k \<R> i))) \<and> (\<exists> (subforest ) . (tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> lang))))"
    proof -
      fix tree
      assume "tree|\<in>|x"
      then obtain state where n76689 : "tree \<in> \<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) state" and "state |\<in>| stateSetFromRuleSet (\<W> n k \<R> i)" using n798 biguplusForests_def     by (smt fimageE forest_language_for_state_def language_for_state_def mem_Collect_eq)  
          
      from n76689 have n655t898 : "(((transition (\<A> i)) (fimage (evaluation (\<A> i)) (childrenSet tree))) (root tree)) = state" using evaluation_def  childrenSet.simps evaluation.simps root.elims
      proof -
        have f1: "evaluation (\<A> i) tree = state"
          using language_for_state_def n76689 by force
        have "\<forall>t. \<exists>f. NODE (root t::abc) f = t"
          by (metis (full_types) root.elims)
        then obtain ff :: "abc tree \<Rightarrow> abc tree fset" where
          f2: "\<And>t. NODE (root t) (ff t) = t"
          by moura
        then have "evaluation (\<A> i) (NODE (root tree) (ff tree)) = state"
          using f1 by (metis (lifting))
        then show ?thesis
          using f2 by (metis childrenSet.simps evaluation.simps)
      qed 
      obtain rule  where n78789 : "states (rule :: (stt,abc) rule) = (fimage (evaluation (\<A> i)) (childrenSet tree))" and n5498 : "symbol rule = root tree"        by (meson rule.select_convs(1) rule.select_convs(2)) 
      then have n766798 : "tree \<in>  \<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) rule" using language_for_rule_def tree_for_rule_def  using n655t898 by (simp add: language_for_rule_def tree_for_rule_def) 
          
      have "rule |\<in>| (rule_set (\<A> i))" using allRulesAreInRuleSet by auto
      then have "rule |\<in>| (ffilter (\<lambda>r. transition (\<A> i) (states r) (symbol r) = state) (rule_set (\<A> i)))" using n655t898 n78789 n5498 by simp
      then have "rule |\<in>| (rulesForState i state)"  using rulesForState_def by auto
      def lang == "\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) rule"
      have "rule |\<in>| (\<Union>|  (rulesForState i |`| stateSetFromRuleSet (\<W> n k \<R> i)))" using \<open>rule |\<in>| rulesForState i state\<close> \<open>state |\<in>| stateSetFromRuleSet (\<W> n k \<R> i)\<close> by auto 
      def subforest == "(finsert tree fempty)"
      have "lang |\<in>| (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<Union>| (rulesForState i |`| stateSetFromRuleSet (\<W> n k \<R> i)))" using \<open>rule |\<in>| \<Union>| (rulesForState i |`| stateSetFromRuleSet (\<W> n k \<R> i))\<close> lang_def by auto 
      have "(tree |\<in>| subforest)" by (simp add: subforest_def) 
      have "subforest |\<subseteq>| x" by (simp add: \<open>tree |\<in>| x\<close> subforest_def) 
      have "subforest \<in> lang"  using lang_def subforest_def n766798 singletonLanguage by auto 
      have "(lang |\<in>| (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<Union>| (rulesForState i |`| stateSetFromRuleSet (\<W> n k \<R> i))) \<and> ( (tree |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> lang)))"
        by (simp add: \<open>lang |\<in>| \<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<Union>| (rulesForState i |`| stateSetFromRuleSet (\<W> n k \<R> i))\<close> \<open>subforest \<in> lang\<close> \<open>subforest |\<subseteq>| x\<close> \<open>tree |\<in>| subforest\<close>) 
      then   show "(\<exists> lang . lang |\<in>| (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<Union>| (rulesForState i |`| stateSetFromRuleSet (\<W> n k \<R> i))) \<and> (\<exists> (subforest ) . (tree |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> lang)))" by auto
    qed
    then show "x \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<Union>| (rulesForState i |`| stateSetFromRuleSet (\<W> n k \<R> i))) " using biguplusForests_def by blast 
  qed
    
  show "\<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<Union>| (rulesForState i |`| stateSetFromRuleSet (\<W> n k \<R> i))) \<subseteq> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) |`| stateSetFromRuleSet (\<W> n k \<R> i))"
  proof
    fix x
    assume n65y87 : " x \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<Union>| (rulesForState i |`| stateSetFromRuleSet (\<W> n k \<R> i)))"
      
    have "(\<And> (tr ) . tr |\<in>| x \<longrightarrow> (\<exists> lang . lang |\<in>| (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) |`| stateSetFromRuleSet (\<W> n k \<R> i)) \<and> (\<exists> (subforest) . (tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> lang)))) "
    proof
      fix tr
      assume n5488976 : " tr |\<in>| x"
      from n65y87 n5488976 biguplusForests_def  have "((\<exists> lang . lang |\<in>| (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<Union>| (rulesForState i |`| stateSetFromRuleSet (\<W> n k \<R> i))) \<and> (\<exists> (subforest) . (tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> lang)))) " by (simp add: biguplusForests_def) 
      then obtain rule lang subforest where n798776 : "lang = \<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) rule" and n767897 : "rule |\<in>| (\<Union>| (rulesForState i |`| stateSetFromRuleSet (\<W> n k \<R> i)))" and "tr |\<in>| subforest" and  "subforest |\<subseteq>| x" and n767987 : "subforest \<in> lang" by blast
       def state == "transition (\<A> i) (states rule) (symbol rule)"
      then have "rule |\<in>| rulesForState i state" using rulesForState_def  using n767897 by auto 
      then have n6587 : "state |\<in>| stateSetFromRuleSet (\<W> n k \<R> i)" using    n767897 by (simp add: fimageE rulesForState_def) 
      def lang2 == "\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) state"
      have "lang2 |\<in>| (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) |`| stateSetFromRuleSet (\<W> n k \<R> i))" using lang2_def n6587 fimageI by auto
      from n767987 state_def lang2_def forest_language_for_rule_def forest_language_for_state_def evaluation_def tree_for_rule_def n798776 langRuleToState have "subforest \<in> \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) state" by auto
      then have "( lang2 |\<in>| (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) |`| stateSetFromRuleSet (\<W> n k \<R> i)) \<and> ( (tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> lang2)))"
        using \<open>lang2 |\<in>| \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) |`| stateSetFromRuleSet (\<W> n k \<R> i)\<close> \<open>subforest |\<subseteq>| x\<close> \<open>tr |\<in>| subforest\<close> lang2_def by auto 
      then show "(\<exists> lang . lang |\<in>| (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) |`| stateSetFromRuleSet (\<W> n k \<R> i)) \<and> (\<exists> (subforest) . (tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> lang)))" by auto
    qed
    then show " x \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) |`| stateSetFromRuleSet (\<W> n k \<R> i))" using biguplusForests_def by blast
  qed
qed
  
    
    
    
    
    
lemma psiRulesStatesLemma2:
  assumes allRulesAreInRuleSet : "\<And>i rule . rule |\<in>| rule_set (\<A> i)"
  shows "\<And>i . ((\<Psi>\<^sub>\<phi> `(\<Uplus> ( ((\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i)) |`|  (stateSetFromRuleSet (\<W> n k \<R> i))))))) = (\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i)) |`| ((\<Union>| (rulesForState i |`| (stateSetFromRuleSet (\<W> n k \<R> i))))))))) "
  using psiRulesStatesLemma21 assms by auto
 
    

    
lemma psiRulesStatesLemma1:
  fixes \<R>
  fixes \<alpha>
  assumes "\<And> \<ii> rule . rule |\<in>| (\<R> \<ii>) \<Longrightarrow> symbol rule = \<alpha>"
  assumes "\<And>i. \<exists> rule . rule |\<in>| \<R> i"
  shows " ((\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma> (stateSetFromRuleSet (\<R> \<aa>\<^sub>1)) (stateSetFromRuleSet (\<R> \<aa>\<^sub>2))))) =
(  factorByRootSymbolF \<alpha> ) `   (\<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2) ))"
proof 
  show "\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma> (stateSetFromRuleSet (\<R> \<aa>\<^sub>1)) (stateSetFromRuleSet (\<R> \<aa>\<^sub>2))) \<subseteq> op \<diamondop> \<alpha> ` \<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))" 
  proof
    fix x
    assume n678 : "x \<in> \<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma> (stateSetFromRuleSet (\<R> \<aa>\<^sub>1)) (stateSetFromRuleSet (\<R> \<aa>\<^sub>2)))"
    then have "x \<in> (\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma> (stateSetFromRuleSet (\<R> \<aa>\<^sub>1)) (stateSetFromRuleSet (\<R> \<aa>\<^sub>2)))"  using \<Z>\<^sub>\<phi>\<^sub>F_subset by blast 
    then have "\<And> i . x \<in> ( ((\<Psi>\<^sub>\<phi> `(\<Oplus> ( (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i)) |`| (stateSetFromRuleSet (\<R> i)))))))" using dist_intersectionLanguageOplus_def  by (metis (full_types) IntE aut_def ot.exhaust)
    then have "\<And>i . \<exists> original . x = \<Psi>\<^sub>\<phi> original \<and> original \<in> (\<Oplus> ( (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i)) |`| (stateSetFromRuleSet (\<R> i))))"              by blast
    then have "\<And>i . \<exists> original . x = \<Psi>\<^sub>\<phi> original \<and> original \<in> (\<Uplus> ( (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i)) |`| (stateSetFromRuleSet (\<R> i)))) \<and>(\<forall> lang. lang |\<in>| (( (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i)) |`| (stateSetFromRuleSet (\<R> i)))) \<longrightarrow> (\<exists> subforest . (subforest \<in> lang \<and> subforest |\<subseteq>| original)))" using bigoplusForests_def by blast
    then have n6587a : "\<And>i . \<exists> original . x = \<Psi>\<^sub>\<phi> original \<and> original \<in> (\<Uplus> ( (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i)) |`| (stateSetFromRuleSet (\<R> i)))) \<and> (\<forall> state. (state |\<in>| stateSetFromRuleSet (\<R> i)) \<longrightarrow> (\<exists> subforest . (subforest \<in> ((\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i)) state) \<and> subforest |\<subseteq>| original)))" using bigoplusForests_def          by (metis (no_types, hide_lams) fimage_eqI) 
    def isGoodOriginal == "\<lambda> i original . x = \<Psi>\<^sub>\<phi> original \<and> original \<in> (\<Uplus> ( (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i)) |`| (stateSetFromRuleSet (\<R> i)))) \<and> (\<forall> state. (state |\<in>| stateSetFromRuleSet (\<R> i)) \<longrightarrow> (\<exists> subforest . (subforest \<in> ((\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i)) state) \<and> subforest |\<subseteq>| original)))"
    from n6587a isGoodOriginal_def have n576897 : "\<And>i . \<exists> original .(isGoodOriginal i original)" by auto
    def originals == "\<lambda> i. (SOME original.   (isGoodOriginal i original))"
    from n576897 originals_def  have n5687 : "\<And>i . (isGoodOriginal i (originals i))"  by (simp add: someI_ex)
    from n5687 isGoodOriginal_def have n6587 : "\<And>i . x = \<Psi>\<^sub>\<phi> (originals i) \<and> (originals i) \<in> (\<Uplus> ( (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i)) |`| (stateSetFromRuleSet (\<R> i)))) \<and> (\<forall> state. (state |\<in>| stateSetFromRuleSet (\<R> i)) \<longrightarrow> (\<exists> subforest . (subforest \<in> ((\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i)) state) \<and> subforest |\<subseteq>| (originals i))))" by auto
    show " x \<in> op \<diamondop> \<alpha> ` \<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))"
    proof -
      have n7687 : "\<And> i rule . rule |\<in>| (\<R> i) \<Longrightarrow> (NODE \<alpha> (ffilter (\<lambda> (tree :: abc tree). (\<exists> state. state |\<in>| ( states rule) \<and> evaluation (\<A> i) tree = state)) (originals i))) \<in> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) rule)"
      proof -
        fix i
        def original == "(originals i)"
        from original_def n6587 have n766897 : "x = \<Psi>\<^sub>\<phi> original \<and> original \<in> (\<Uplus> ( (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i)) |`| (stateSetFromRuleSet (\<R> i)))) \<and> (\<forall> state. (state |\<in>| stateSetFromRuleSet (\<R> i)) \<longrightarrow> (\<exists> subforest . (subforest \<in> ((\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i)) state) \<and> subforest |\<subseteq>| original)))" by blast
        hence n1 : "x = \<Psi>\<^sub>\<phi> original" and n2 : "original \<in> (\<Uplus> ( (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i)) |`| (stateSetFromRuleSet (\<R> i))))" and n3 : "(\<forall> state. (state |\<in>| stateSetFromRuleSet (\<R> i)) \<longrightarrow> (\<exists> subforest . (subforest \<in> ((\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i)) state) \<and> subforest |\<subseteq>| original)))" by auto
        fix rule
        assume n7687 : "rule |\<in>| (\<R> i)"
        def treesForStates  == "ffilter (\<lambda> (tree :: abc tree). (\<exists> state. state |\<in>| ( states rule) \<and> evaluation (\<A> i) tree = state)) original"
        def newTree == "(NODE \<alpha> treesForStates)"
        have "newTree \<in> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) rule)" using treesForStates_def newTree_def
        proof (simp add:  language_for_rule_def)
          show " tree_for_rule (\<A> i) rule (NODE \<alpha> (ffilter (\<lambda>tree. evaluation (\<A> i) tree |\<in>|  states rule) original))"
          proof (simp add : tree_for_rule_def)
            show "\<alpha> = symbol rule \<and> evaluation (\<A> i) |`| ffilter (\<lambda>tree. evaluation (\<A> i) tree |\<in>|  states rule) original = states rule"
            proof
              show "\<alpha> = symbol rule" using assms(1) n7687 by auto
              show " evaluation (\<A> i) |`| ffilter (\<lambda>tree. evaluation (\<A> i) tree |\<in>|  states rule) original = states rule" 
              proof
                show "states rule |\<subseteq>| evaluation (\<A> i) |`| ffilter (\<lambda>tree. evaluation (\<A> i) tree |\<in>|  states rule) original" 
                proof
                  fix x
                  assume "x |\<in>| states rule"
                  then have "x |\<in>| stateSetFromRuleSet (\<R> i)" using stateSetFromRuleSet_def n7687
                  proof -
                    have "states rule |\<in>| states |`| \<R> i"   using n7687 by blast
                    then have "x |\<in>| \<Union>| (states |`| \<R> i)"   using \<open>x |\<in>| states rule\<close> by blast
                    then show ?thesis  by (metis stateSetFromRuleSet_def)
                  qed 
                  then obtain subforest where n7y687 : "subforest \<in> ((\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i)) x) \<and> subforest |\<subseteq>| original"   using n3 by auto
                  then obtain tree where nu668i7 : "tree |\<in>| subforest" using forest_language_for_state_def                          by fastforce 
                  then have "evaluation (\<A> i) tree = x" using n7y687 forest_language_for_state_def                             by (simp add: forest_language_for_state_def)   
                  then show "x |\<in>| evaluation (\<A> i) |`| ffilter (\<lambda>tree. evaluation (\<A> i) tree |\<in>| states rule) original" using n7y687                                using \<open>x |\<in>| states rule\<close> nu668i7 by auto 
                qed
                show "evaluation (\<A> i) |`| ffilter (\<lambda>tree. evaluation (\<A> i) tree |\<in>|  states rule) original |\<subseteq>| states rule" by auto
              qed
            qed
          qed
        qed
        then   show "NODE \<alpha> (ffilter (\<lambda>tree. \<exists>state. state |\<in>| states rule \<and> evaluation (\<A> i) tree = state) original) \<in> \<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) rule"  using newTree_def treesForStates_def by auto
      qed
      def newForests == "(\<lambda> i . ( \<lambda> rule. (NODE \<alpha> (ffilter (\<lambda> (tree :: abc tree). (\<exists> state. state |\<in>| ( states rule) \<and> evaluation (\<A> i) tree = state)) (originals i)))) |`| (\<R> i))"
      have n6568i7 : "\<And>i . (newForests i) \<in> ( (((\<Oplus> ( (\<L>\<^sub>\<phi>\<^sub>\<rho>  (\<A> i) ) |`| (\<R> i)))))) "
      proof (simp add : bigoplusForests_def)
        fix i
        show "(newForests i) \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i) \<and> (\<forall>lang. lang |\<in>| \<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i \<longrightarrow> (\<exists>subforest. subforest \<in> lang \<and> subforest |\<subseteq>| (newForests i)))"
        proof
          show "(newForests i) \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i)" 
          proof (simp add : biguplusForests_def)
            show " \<forall>tr. tr |\<in>| (newForests i) \<longrightarrow> (\<exists>lang. lang |\<in>| \<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| (newForests i) \<and> subforest \<in> lang))"
            proof
              fix tr
              show "tr |\<in>| (newForests i) \<longrightarrow> (\<exists>lang. lang |\<in>| \<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| (newForests i) \<and> subforest \<in> lang))"
              proof
                assume "tr |\<in>| (newForests i)" 
                from newForests_def obtain rule where "rule |\<in>| (\<R> i)" and n7897 : "tr = (NODE \<alpha> (ffilter (\<lambda> (tree :: abc tree). (\<exists> state. state |\<in>| ( states rule) \<and> evaluation (\<A> i) tree = state)) (originals i)))"
                  using \<open>tr |\<in>| (newForests i)\<close> by blast 
                def lang == "\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) rule"
                then have "lang |\<in>| \<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i"
                  by (simp add: \<open>rule |\<in>| \<R> i\<close>) 
                def subforest == "finsert tr fempty"
                from subforest_def have "tr |\<in>| subforest"
                  by auto 
                from subforest_def newForests_def   have "subforest |\<subseteq>| (newForests i)"
                  using \<open>tr |\<in>| (newForests i)\<close> by blast 
                from subforest_def n7687 lang_def n7897 have "subforest \<in> lang"
                  by (simp add: \<open>rule |\<in>| \<R> i\<close> singletonLanguage) 
                then show "(\<exists>lang. lang |\<in>| \<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| (newForests i) \<and> subforest \<in> lang))"
                  using \<open>lang |\<in>| \<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i\<close> \<open>subforest |\<subseteq>| (newForests i)\<close> \<open>tr |\<in>| subforest\<close> by blast 
              qed
            qed
          qed
          show " \<forall>lang. lang |\<in>| \<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i \<longrightarrow> (\<exists>subforest. subforest \<in> lang \<and> subforest |\<subseteq>| (newForests i))"
          proof
            fix lang
            show "lang |\<in>| \<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i \<longrightarrow> (\<exists>subforest. subforest \<in> lang \<and> subforest |\<subseteq>| (newForests i))"
            proof
              assume "lang |\<in>| \<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i"
              then obtain rule where n7656876 : "rule |\<in>| \<R> i" and "lang = \<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) rule" by auto
              show "\<exists>subforest. subforest \<in> lang \<and> subforest |\<subseteq>| (newForests i)"
              proof -
                def subforest == "(finsert (NODE \<alpha> (ffilter (\<lambda> (tree :: abc tree). (\<exists> state. state |\<in>| ( states rule) \<and> evaluation (\<A> i) tree = state)) (originals i))) fempty) "
                have "subforest \<in> lang \<and> subforest |\<subseteq>| (newForests i)"
                proof
                  show "subforest \<in> lang"
                    using \<open>\<And>rule. rule |\<in>| \<R> i \<Longrightarrow> NODE \<alpha> (ffilter (\<lambda>tree. \<exists>state. state |\<in>| states rule \<and> evaluation (\<A> i) tree = state) (originals i)) \<in> \<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) rule\<close> \<open>lang = \<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) rule\<close> \<open>rule |\<in>| \<R> i\<close> singletonLanguage subforest_def by auto 
                  show "subforest |\<subseteq>| (newForests i)" 
                  proof
                    fix x
                    assume "x |\<in>| subforest"
                    then have "x = (NODE \<alpha> (ffilter (\<lambda> (tree :: abc tree). (\<exists> state. state |\<in>| ( states rule) \<and> evaluation (\<A> i) tree = state)) (originals i)))" using subforest_def                            by blast 
                    then show "x |\<in>| (newForests i)" using  newForests_def n7656876 by auto
                  qed
                qed
                then show "\<exists>subforest. subforest \<in> lang \<and> subforest |\<subseteq>| (newForests i)" by auto
              qed
            qed
          qed
        qed
      qed
      then have "\<And>i . ((\<lambda> rule. (NODE \<alpha> (ffilter (\<lambda> (tree :: abc tree). (\<exists> state. state |\<in>| ( states rule) \<and> evaluation (\<A> i) tree = state)) (originals i)))) |`| (\<R> i)) \<in> ( (((\<Oplus> ( (\<L>\<^sub>\<phi>\<^sub>\<rho>  (\<A> i) ) |`| (\<R> i)))))) " 
        using newForests_def by auto
      have n65987 : "\<And>i . psiF (newForests i) = (finsert (NODE \<alpha> x) fempty)"
      proof -
        fix i
        from n6587 have n6545877 : "x = \<Psi>\<^sub>\<phi> (originals i)" by auto
        from n6587 have "(originals i) \<in> (\<Uplus> ( (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i)) |`| (stateSetFromRuleSet (\<R> i))))" by auto
        from n6587 have "(\<forall> state. (state |\<in>| stateSetFromRuleSet (\<R> i)) \<longrightarrow> (\<exists> subforest . (subforest \<in> ((\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i)) state) \<and> subforest |\<subseteq>| (originals i))))" by auto
            
        from n6545877 psiF_def have   n767897 :    "x = fimage (\<lambda> symbol2 .
                              psi (NODE symbol2 (\<Union>| (fimage childrenSet (childrenWithSymbol symbol2 (originals i))))
                                  )
                              )
                              (fimage root (originals i))" by auto
        
        from n6545877 have "x = fimage (\<lambda> symbol2 .
                              psi (NODE symbol2 (\<Union>| (fimage childrenSet (childrenWithSymbol symbol2 (originals i))))
                                  )
                              )
                              (fimage root (originals i))" using psiF_def by auto
        then have "(finsert (NODE \<alpha> x) fempty) = (finsert (NODE \<alpha> (fimage (\<lambda> symbol2 .
                              psi (NODE symbol2 (\<Union>| (fimage childrenSet (childrenWithSymbol symbol2 (originals i))))
                                  )
                              )
                              (fimage root (originals i)))) fempty)" by auto
        have n6768998 : "psiF (newForests i) = fimage (\<lambda> symbol2 .
                              psi (NODE symbol2 (\<Union>| (fimage childrenSet (childrenWithSymbol symbol2 (newForests i))))
                                  )
                              )
                              (fimage root (newForests i))" using psiF_def  by auto
        have n6557 : "\<And> tr . tr |\<in>| (newForests i) \<Longrightarrow> root tr = \<alpha>" using newForests_def by auto
        have n5445786 : " (fimage root (newForests i)) = (finsert \<alpha> fempty)" proof
          
          from n6557 show " root |`| (newForests i) |\<subseteq>| {|\<alpha>|}" by auto
          have "\<exists> tr . tr |\<in>| (newForests i) \<and> root tr = \<alpha>" 
          proof (simp add : newForests_def)
            have "\<exists> rule . rule |\<in>| \<R> i" using assms(2) by auto
            then show "\<exists>tr. tr |\<in>| (\<lambda>rule. NODE \<alpha> (ffilter (\<lambda>tree. evaluation (\<A> i) tree |\<in>| states rule) (originals i))) |`| \<R> i \<and> root tr = \<alpha>" by auto
          qed
          then show " {|\<alpha>|} |\<subseteq>| root |`| (newForests i)" by auto
        qed
        from n6768998 n5445786 have "psiF (newForests i) = (finsert (psi (NODE \<alpha> (\<Union>| (fimage childrenSet (childrenWithSymbol \<alpha> (newForests i)))))) fempty)" by auto
        have n65876 :  "(childrenWithSymbol \<alpha> (newForests i)) = (newForests i)" 
        proof (simp add : childrenWithSymbol_def)
          show "inf_fset2 (newForests i) {child1. root child1 = \<alpha>} = (newForests i)"
          proof
            show "inf_fset2 (newForests i) {child1. root child1 = \<alpha>} |\<subseteq>| (newForests i)"
              by (simp add: finter_lower1) 
            show "(newForests i) |\<subseteq>| inf_fset2 (newForests i) {child1. root child1 = \<alpha>} " using n6557
              by (simp add: finterI fsubsetI) 
          qed
        qed
        have n65787 : "\<Union>| (fimage childrenSet (newForests i)) = (originals i)"
        proof (simp add : newForests_def)
          show "\<Union>| ((childrenSet \<circ> (\<lambda>rule. NODE \<alpha> (ffilter (\<lambda>tree. evaluation (\<A> i) tree |\<in>| states rule) (originals i)))) |`| \<R> i) = (originals i)"
          proof 
            show " \<Union>| ((childrenSet \<circ> (\<lambda>rule. NODE \<alpha> (ffilter (\<lambda>tree. evaluation (\<A> i) tree |\<in>| states rule) (originals i)))) |`| \<R> i) |\<subseteq>| (originals i)"
            proof
              show "\<And>x. x |\<in>| \<Union>| ((childrenSet \<circ> (\<lambda>rule. NODE \<alpha> (ffilter (\<lambda>tree. evaluation (\<A> i) tree |\<in>| states rule) (originals i)))) |`| \<R> i) \<Longrightarrow> x |\<in>| originals i"
              proof -
                fix x
                assume "x |\<in>| \<Union>| ((childrenSet \<circ> (\<lambda>rule. NODE \<alpha> (ffilter (\<lambda>tree. evaluation (\<A> i) tree |\<in>| states rule) (originals i)))) |`| \<R> i)"
                then obtain rule where "rule |\<in>| \<R> i" and "x |\<in>| ((childrenSet \<circ> (\<lambda>rule. NODE \<alpha> (ffilter (\<lambda>tree. evaluation (\<A> i) tree |\<in>| states rule) (originals i))))) rule" by auto
                then have "x |\<in>| ((childrenSet(  (NODE \<alpha> (ffilter (\<lambda>tree. evaluation (\<A> i) tree |\<in>| states rule) (originals i))))))" by auto
                then have "x |\<in>|                (ffilter (\<lambda>tree. evaluation (\<A> i) tree |\<in>| states rule) (originals i))" by auto
                then show "x |\<in>| originals i" by auto
                qed
              qed
            show " (originals i) |\<subseteq>| \<Union>| ((childrenSet \<circ> (\<lambda>rule. NODE \<alpha> (ffilter (\<lambda>tree. evaluation (\<A> i) tree |\<in>| states rule) (originals i)))) |`| \<R> i)" 
            proof
              fix x
              assume n6787 : "x |\<in>| (originals i)"
              show " x |\<in>| \<Union>| ((childrenSet \<circ> (\<lambda>rule. NODE \<alpha> (ffilter (\<lambda>tree. evaluation (\<A> i) tree |\<in>| states rule) (originals i)))) |`| \<R> i) "
              proof                    (simp add : ffUnionLemma)
                
                show "x |\<in>| (originals i) \<and> fBex (\<R> i) (\<lambda>rule. evaluation (\<A> i) x |\<in>| states rule)"
                proof              
                  from n6787 show "x |\<in>| (originals i)" by auto
                  from n6587 have " (originals i) \<in> (\<Uplus> ( (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i)) |`| (stateSetFromRuleSet (\<R> i))))" by auto 
                  hence "\<exists> lang . lang |\<in>| ( (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i)) |`| (stateSetFromRuleSet (\<R> i))) \<and> (\<exists> (subforest ) . (x |\<in>| subforest \<and> subforest |\<subseteq>| (originals i) \<and> subforest \<in> lang))" using n6787 biguplusForests_def by blast
                  then obtain lang where n76767987 : " lang |\<in>| ( (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i)) |`| (stateSetFromRuleSet (\<R> i))) \<and> (\<exists> (subforest ) . (x |\<in>| subforest \<and> subforest |\<subseteq>| (originals i) \<and> subforest \<in> lang))" by auto
                  then obtain rule state where "lang = \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) state" and "state |\<in>| states rule" and "rule |\<in>| (\<R> i)" using stateSetFromRuleSet_def
                    by (metis (no_types, lifting) fimageE n67789564) 
                  hence "evaluation (\<A> i) x = state" using forest_language_for_state_def n76767987   by (smt mem_Collect_eq) 
                  then show "fBex (\<R> i) (\<lambda>rule. evaluation (\<A> i) x |\<in>| states rule)"    using \<open>rule |\<in>| \<R> i\<close> \<open>state |\<in>| states rule\<close> by auto 
                qed
              qed
            qed
          qed
        qed
        have "(psi (NODE \<alpha> (originals i))) = (NODE \<alpha> (fimage (\<lambda> symbol2 .
                              psi (NODE symbol2 (\<Union>| (fimage childrenSet (childrenWithSymbol symbol2 (originals i))))
                                  )
                              )
                              (fimage root (originals i))))" using psiDef          by blast 
        hence "(psi (NODE \<alpha> (\<Union>| (fimage childrenSet (newForests i))))) = (NODE \<alpha> (fimage (\<lambda> symbol2 .
                              psi (NODE symbol2 (\<Union>| (fimage childrenSet (childrenWithSymbol symbol2 (originals i))))
                                  )
                              )
                              (fimage root (originals i))))" using n65787 by auto
        hence "(psi (NODE \<alpha> (\<Union>| (fimage childrenSet (childrenWithSymbol \<alpha>  (newForests i)))))) = (NODE \<alpha> (fimage (\<lambda> symbol2 .
                              psi (NODE symbol2 (\<Union>| (fimage childrenSet (childrenWithSymbol symbol2 (originals i))))
                                  )
                              )
                              (fimage root (originals i))))" using n65876 by auto
        hence "(finsert (psi (NODE \<alpha> (\<Union>| (fimage childrenSet (childrenWithSymbol \<alpha>  (newForests i)))))) fempty) = (finsert (NODE \<alpha> (fimage (\<lambda> symbol2 .
                              psi (NODE symbol2 (\<Union>| (fimage childrenSet (childrenWithSymbol symbol2 (originals i))))
                                  )
                              )
                              (fimage root (originals i)))) fempty)" by auto
        then show "psiF (newForests i) = (finsert (NODE \<alpha> x) fempty)"  by (simp add: \<open>\<Psi>\<^sub>\<phi> (newForests i) = {|psi (NODE \<alpha> (\<Union>| (childrenSet |`| childrenWithSymbol \<alpha> (newForests i))))|}\<close> n767897)  
      qed
      then have "\<And>i .x = \<alpha> \<diamondop> \<Psi>\<^sub>\<phi> (newForests i)"
      proof (simp add : factorByRootSymbolF_lemma)
        have "fset x = {t. ((t |\<in>| x))}"
        proof
          show "fset x \<subseteq> {t. t |\<in>| x}" using notin_fset
            by fastforce 
          show "{t. t |\<in>| x} \<subseteq> fset x"  using notin_fset
            by fastforce
        qed
          
        hence "fset x = {t. ((root (NODE \<alpha> x) = \<alpha> \<and> t |\<in>| childrenSet (NODE \<alpha> x)))}" using root.simps childrenSet.simps by auto
        hence "fset x = {t. (\<exists>tree. tree = (NODE \<alpha> x) \<and> (root tree = \<alpha> \<and> t |\<in>| childrenSet tree))}" by auto
        hence "fset x = {t. (\<exists>tree. tree |\<in>| {|NODE \<alpha> x|} \<and> (root tree = \<alpha> \<and> t |\<in>| childrenSet tree))}" by auto
            
        then show "x = \<alpha> \<diamondop> {|NODE \<alpha> x|}" using factorByRootSymbolF_lemma factorByRootSymbol_def by auto
      qed
        
        
      have "{|NODE \<alpha> x|} \<in> \<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))"
      proof (simp add : \<Z>\<^sub>\<phi>\<Z>\<^sub>\<phi>\<^sub>Flemma \<Z>\<^sub>\<phi>_def notin_fset)
        have "{|NODE \<alpha> x|} \<in> fset (boundedForests (Suc n))" 
        proof (simp add : restrictionIsFiniteForests)
          have "\<And> tr . tr |\<in>| x \<Longrightarrow> height tr \<le> n"
            using \<Z>\<^sub>\<phi>\<^sub>F_def n678 by auto 
          then show "maxFset (height |`| x) \<le> n"     by (metis (mono_tags, lifting) fimageE finiteMaxExists(2) finiteMaxExists(3) le_0_eq nat_le_linear) 
          then have "{|NODE \<alpha> x|} |\<in>| (boundedForests (Suc n))" using heightSingleton by auto
          have "{|NODE \<alpha> x|} \<in> (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))" 
          proof (simp add : dist_intersectionLanguageOplusRules_def)
            show "{|NODE \<alpha> x|} \<in> \<Psi>\<^sub>\<phi> ` \<Oplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1 |`| \<R> \<aa>\<^sub>1) \<and> {|NODE \<alpha> x|} \<in> \<Psi>\<^sub>\<phi> ` \<Oplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>2 |`| \<R> \<aa>\<^sub>2)"
            proof
              have n65576 : "\<And>i . ( {|NODE \<alpha> x|} \<in> \<Psi>\<^sub>\<phi> ` \<Oplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i))"
              proof 
                fix i
                from n65987 show "{|NODE \<alpha> x|} = \<Psi>\<^sub>\<phi> (newForests i)" by auto
                show "(newForests i) \<in> \<Oplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i)"  by (simp add: n6568i7) 
              qed
              from n65576  show "{|NODE \<alpha> x|} \<in> \<Psi>\<^sub>\<phi> ` \<Oplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1 |`| \<R> \<aa>\<^sub>1)"                by (metis aut_def)  
              from n65576 show "{|NODE \<alpha> x|} \<in> \<Psi>\<^sub>\<phi> ` \<Oplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>2 |`| \<R> \<aa>\<^sub>2)"                  by (metis aut_def)
            qed
          qed
        qed
        show "{|NODE \<alpha> x|} \<in> fset (inf_fset2 (boundedForests (Suc n)) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2)))"
          by (metis (no_types, lifting) IntI \<open>\<And>i. (\<lambda>rule. NODE \<alpha> (ffilter (\<lambda>tree. \<exists>state. state |\<in>| states rule \<and> evaluation (\<A> i) tree = state) (originals i))) |`| \<R> i \<in> \<Oplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i)\<close> \<open>{|NODE \<alpha> x|} \<in> fset (boundedForests (Suc n))\<close> aut_def dist_intersectionLanguageOplusRules_def finterI image_eqI n65987 newForests_def notin_fset) 
      qed
        
      have " x = \<alpha> \<diamondop> {|NODE \<alpha> x|}"
      proof -
        have n7656876 : "\<And>a. ((a |\<in>| \<alpha> \<diamondop> {|NODE \<alpha> x|}) = (a \<in> factorByRootSymbol \<alpha> (fset {|NODE \<alpha> x|})))" using factorByRootSymbolF_lemma by auto
        have a1 : "(NODE \<alpha> x) \<in> (fset {|NODE \<alpha> x|})" by auto
        have a2 : "root (NODE \<alpha> x) = \<alpha>" by auto
        have a3 : "x = (childrenSet (NODE \<alpha> x))" by auto
        from a1 a2 a3 have "\<And>a. ((a |\<in>| x) = (a \<in> factorByRootSymbol \<alpha> (fset {|NODE \<alpha> x|})))" using factorByRootSymbol_def by auto
        then show " x = \<alpha> \<diamondop> {|NODE \<alpha> x|}" using n7656876 by auto
      qed
      show "x \<in> op \<diamondop> \<alpha> ` \<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))" using \<open>x = \<alpha> \<diamondop> {|NODE \<alpha> x|}\<close> \<open>{|NODE \<alpha> x|} \<in> \<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))\<close> by auto
    qed
      
  qed
  show "op \<diamondop> \<alpha> ` \<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2)) \<subseteq> \<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma> (stateSetFromRuleSet (\<R> \<aa>\<^sub>1)) (stateSetFromRuleSet (\<R> \<aa>\<^sub>2)))" 
  proof 
    show "\<And>x. x \<in> op \<diamondop> \<alpha> ` \<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2)) \<Longrightarrow> x \<in> \<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma> (stateSetFromRuleSet (\<R> \<aa>\<^sub>1)) (stateSetFromRuleSet (\<R> \<aa>\<^sub>2)))"
    proof -
      fix x
      assume "x \<in> op \<diamondop> \<alpha> ` \<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))"
      then obtain forest where n75656876 : "forest \<in> \<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))" and n5466876 : "x = \<alpha> \<diamondop> forest" by auto
      hence n6578i7 : "fset x = {t. (\<exists>tree. tree  |\<in>| forest \<and> (root tree = \<alpha> \<and> t |\<in>| childrenSet tree))}"   by (smt Collect_cong factorByRootSymbolF_lemma(2) factorByRootSymbol_def notin_fset)  
          
      show "x \<in> \<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma> (stateSetFromRuleSet (\<R> \<aa>\<^sub>1)) (stateSetFromRuleSet (\<R> \<aa>\<^sub>2)))" 
      proof (simp add : \<Z>\<^sub>\<phi>\<Z>\<^sub>\<phi>\<^sub>Flemma \<Z>\<^sub>\<phi>_def notin_fset)
        
        have u1 : "x |\<in>| (boundedForests n)"
        proof -
          have "\<And>tr . tr |\<in>| x \<Longrightarrow> height tr \<le> n"
          proof -
            fix tr
            assume "tr |\<in>| x"
            then obtain t where "(\<exists>tree. tree  |\<in>| forest \<and> (root tree = \<alpha> \<and> t |\<in>| childrenSet tree))" using n6578i7 notin_fset  by (smt bot_fset.rep_eq empty_Collect_eq fempty_iff) 
            then obtain tree where "tree  |\<in>| forest" and n76576 : "tr |\<in>| childrenSet tree"
              using \<open>tr |\<in>| x\<close> \<open>x = \<alpha> \<diamondop> forest\<close> factorByRootSymbolF_lemma(1) factorByRootSymbolF_lemma(2) n6578i7 by blast 
            then have "height tree \<le> Suc n" using n75656876 \<Z>\<^sub>\<phi>\<Z>\<^sub>\<phi>\<^sub>Flemma \<Z>\<^sub>\<phi>_def restrictionIsFiniteForests
            proof -
              show ?thesis using \<Z>\<^sub>\<phi>\<^sub>F_def \<open>tree |\<in>| forest\<close> n75656876 by force
            qed 
            then show "height tr \<le> n" using n76576
              by (meson heightOfChild leD leI less_trans_Suc) 
          qed
          then have "x \<in> (fset (boundedForests n))"           using     restrictionIsFiniteForests by blast
          then show "x |\<in>| (boundedForests n)"           using  notin_fset by fastforce
        qed
          
        have u2 : "x \<in> (\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma> (stateSetFromRuleSet (\<R> \<aa>\<^sub>1)) (stateSetFromRuleSet (\<R> \<aa>\<^sub>2)))" 
        proof (simp add : dist_intersectionLanguageOplus_def)
          have "\<And>i . x \<in> \<Psi>\<^sub>\<phi> ` \<Oplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) |`| stateSetFromRuleSet (\<R> i))"
          proof -
            fix i
            show "x \<in> \<Psi>\<^sub>\<phi> ` \<Oplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) |`| stateSetFromRuleSet (\<R> i))"
            proof
              
              def originalForest == "SOME originalForest. forest = \<Psi>\<^sub>\<phi> originalForest \<and> originalForest \<in> (\<Oplus> ( (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i)) |`| (\<R> i)))"
                
                
              from n75656876 have "forest \<in> \<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))" by auto
              then have  "forest \<in> (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))"
                using \<Z>\<^sub>\<phi>\<^sub>F_subset by blast 
              then have "forest \<in> ( ((\<Psi>\<^sub>\<phi> `(\<Oplus> ( (\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| (\<R> \<aa>\<^sub>1)))) 
                            \<inter> (\<Psi>\<^sub>\<phi> ` (\<Oplus> ((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>2) |`| (\<R> \<aa>\<^sub>2))))))"      using dist_intersectionLanguageOplusRules_def by auto
              then have "forest \<in> ( ((\<Psi>\<^sub>\<phi> `(\<Oplus> ( (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i)) |`| (\<R> i))))))"
                by (metis (full_types) Int_iff aut_def ot.exhaust) 
              then have n65876 : "\<exists> originalForest. forest = \<Psi>\<^sub>\<phi> originalForest \<and> originalForest \<in> (\<Oplus> ( (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i)) |`| (\<R> i)))" by auto
              have  n656987 :  "forest = \<Psi>\<^sub>\<phi> originalForest \<and> originalForest \<in> (\<Oplus> ( (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i)) |`| (\<R> i)))" 
              proof (simp add : originalForest_def someI_ex)
                from n65876 show "forest = \<Psi>\<^sub>\<phi> (SOME originalForest. forest = \<Psi>\<^sub>\<phi> originalForest \<and> originalForest \<in> \<Oplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i)) \<and>
    (SOME originalForest. forest = \<Psi>\<^sub>\<phi> originalForest \<and> originalForest \<in> \<Oplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i)) \<in> \<Oplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i)"
                  by (metis (mono_tags, lifting) someI_ex) 
              qed
              then have "forest = \<Psi>\<^sub>\<phi> originalForest" and n7687 : "originalForest \<in> (\<Oplus> ( (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i)) |`| (\<R> i)))" using originalForest_def by auto
                  
                  
              from n5466876 have  "x = \<alpha> \<diamondop> forest" by auto
              from n6578i7 have "fset x = {t. (\<exists>tree. tree  |\<in>| forest \<and> (root tree = \<alpha> \<and> t |\<in>| childrenSet tree))}"  by auto
                  
                  
              def childrenInTheOriginalForest == "\<Union>| (childrenSet |`| originalForest)"
              show "x = \<Psi>\<^sub>\<phi> childrenInTheOriginalForest"
              proof -
                from n5466876 have  "x = \<alpha> \<diamondop> forest" by auto
                from n6578i7 have "fset x = {t. (\<exists>tree. tree  |\<in>| forest \<and> (root tree = \<alpha> \<and> t |\<in>| childrenSet tree))}"  by auto
                from n656987 have  "forest = \<Psi>\<^sub>\<phi> originalForest \<and> originalForest \<in> (\<Oplus> ( (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i)) |`| (\<R> i)))"  by auto
                    
                from n5466876 n656987 have n6556897 : "x = \<alpha> \<diamondop> ( \<Psi>\<^sub>\<phi> originalForest)" by auto
                    
                from psiF_def  
                have n76897 : "\<Psi>\<^sub>\<phi> childrenInTheOriginalForest
                    = (\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 childrenInTheOriginalForest)))) |`| root |`| childrenInTheOriginalForest" by auto
                
                
                from n6556897 psiF_def have n6556897a :                      "x = \<alpha> \<diamondop> (((\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 originalForest)))) |`| root |`| originalForest))"                by (simp add: psiF_def)
                have n76867 : "\<And> x . x |\<in>| originalForest \<Longrightarrow> root x = \<alpha>"
                proof -
                  fix x
                  assume n768643547 : " x |\<in>| originalForest"
                  from n7687 have "originalForest \<in> (\<Oplus> ( (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i)) |`| (\<R> i)))" by auto
                  then show "root x = \<alpha>" using assms(1)  n768643547 using fixOplusRulesRoot by auto
                qed
                  
                  from assms(2) have n76987987 :  "\<exists> rule. rule |\<in>| \<R> i" by auto
                  
                from n7687 have "originalForest \<in> \<Oplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i)" by auto
                    
                then have n65687 : "\<exists> z . z |\<in>| originalForest" using bigoplusForests_def biguplusForests_def forest_language_for_rule_def n76987987
                  by (smt fimage_eqI fsubsetI fsubset_antisym mem_Collect_eq)
                  
                  from n76867 n65687 have n76867a : "root |`| originalForest = (finsert \<alpha> fempty)" by auto
                      
                  have  n65786 :  "(\<Union>| (childrenSet |`| childrenWithSymbol \<alpha> originalForest)) = childrenInTheOriginalForest" 
                  proof (simp add : childrenInTheOriginalForest_def)
                    have "childrenWithSymbol \<alpha> originalForest = originalForest"
                    proof (simp add : childrenWithSymbol_def)
                      show "inf_fset2 originalForest {child1. root child1 = \<alpha>} = originalForest" using n76867    by (simp add: fequalityI finterI finter_lower1 fsubsetI) 
                    qed
                    then show "\<Union>| (childrenSet |`| childrenWithSymbol \<alpha> originalForest) = \<Union>| (childrenSet |`| originalForest)" by simp
                  qed
                    
                    
                from factorPsiLemma  have n65876 : "\<And>children . (\<alpha> \<diamondop> (finsert ((psi (NODE \<alpha> children))) fempty)) = \<Psi>\<^sub>\<phi> children" by auto
                    
                from n65786   n65876 have   "\<alpha> \<diamondop> (finsert ((psi (NODE \<alpha> (\<Union>| (childrenSet |`| childrenWithSymbol \<alpha> originalForest))))) fempty) = \<Psi>\<^sub>\<phi> childrenInTheOriginalForest" by auto
                then have   "\<alpha> \<diamondop> (((\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 originalForest)))) |`| (finsert \<alpha> fempty))) = \<Psi>\<^sub>\<phi> childrenInTheOriginalForest" by auto
                hence n659878 : "\<alpha> \<diamondop> (((\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 originalForest)))) |`| root |`| originalForest)) = \<Psi>\<^sub>\<phi> childrenInTheOriginalForest" using n76867a by auto
                have "\<Psi>\<^sub>\<phi> childrenInTheOriginalForest                  = \<alpha> \<diamondop> ( \<Psi>\<^sub>\<phi> originalForest)"                using n6556897 n6556897a n659878 by auto
                then show "x = \<Psi>\<^sub>\<phi> childrenInTheOriginalForest" using n76897 n6556897 by auto
              qed
                
              show "childrenInTheOriginalForest \<in> \<Oplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) |`| stateSetFromRuleSet (\<R> i))" 
              proof (simp add : bigoplusForests_def)
                show "childrenInTheOriginalForest \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) |`| stateSetFromRuleSet (\<R> i)) \<and> (\<forall>lang. lang |\<in>| \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) |`| stateSetFromRuleSet (\<R> i) \<longrightarrow> (\<exists>subforest. subforest \<in> lang \<and> subforest |\<subseteq>| childrenInTheOriginalForest))"
                proof
                  show "childrenInTheOriginalForest \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) |`| stateSetFromRuleSet (\<R> i))" 
                  proof (simp add : childrenInTheOriginalForest_def)
                    
                    have "(\<And> (tr ) . tr |\<in>| (\<Union>| (childrenSet |`| originalForest)) \<Longrightarrow> (\<exists> lang . lang |\<in>|  (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) |`| stateSetFromRuleSet (\<R> i)) \<and> (\<exists> (subforest ) . (tr |\<in>| subforest \<and> subforest |\<subseteq>|  (\<Union>| (childrenSet |`| originalForest)) \<and> subforest \<in> lang))))"
                    proof -
                      fix tr
                      assume n7567987 : " tr |\<in>| \<Union>| (childrenSet |`| originalForest)"
                      then obtain tree where n654786 : "tr |\<in>| childrenSet tree" and n742687 : "tree |\<in>| originalForest" by auto
                      from n7687 have " originalForest \<in> \<Oplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i) " by auto
                      then have "originalForest \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i) " using bigoplusForests_def by auto
                      then obtain lang subforest where "lang |\<in>| \<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i" and n76864 : " (tree |\<in>| subforest \<and> subforest |\<subseteq>| originalForest \<and> subforest \<in> lang)"  using n742687 biguplusForests_def by (smt mem_Collect_eq) 
                      then obtain rule where n645687 : "rule |\<in>| \<R> i" and n6568io7 : "lang = \<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) rule" by auto
                      from forest_language_for_rule_def n76864 n742687 n6568io7 have "tree_for_rule (\<A> i) rule tree" by auto
                      then obtain state where "state = (evaluation  (\<A> i)) tr" and n656987 : "state |\<in>| states rule" using tree_for_rule_def n654786
                        by (metis fimage_eqI) 
                          then have "tr \<in> \<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) state"
                            by (simp add: language_for_state_def) 
                          then have n65587 : "(finsert tr fempty) \<in> \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) state" using singletonRuleLang by auto
                          def subforest == "(finsert tr fempty)"
                            
                          def lang == "\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) state"
                            
                          
                          have " lang |\<in>|  (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) |`| stateSetFromRuleSet (\<R> i)) \<and>  (tr |\<in>| subforest \<and> subforest |\<subseteq>|  (\<Union>| (childrenSet |`| originalForest)) \<and> subforest \<in> lang)"
                          proof
                            have "state |\<in>| stateSetFromRuleSet (\<R> i)" using n656987  n645687  by (simp add:stateRuleSet)
                            then show "lang |\<in>| \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) |`| stateSetFromRuleSet (\<R> i)" using lang_def by auto
                            show "tr |\<in>| subforest \<and> subforest |\<subseteq>| \<Union>| (childrenSet |`| originalForest) \<and> subforest \<in> lang"
                            proof
                              show "tr |\<in>| subforest" using subforest_def by auto
                              show "subforest |\<subseteq>| \<Union>| (childrenSet |`| originalForest) \<and> subforest \<in> lang"
                              proof
                                show "subforest |\<subseteq>| \<Union>| (childrenSet |`| originalForest)" using subforest_def n7567987
                                  by simp
                                show "subforest \<in> lang" using n65587 subforest_def lang_def by auto
                              qed
                            qed
                          qed
                          then show "(\<exists> lang . lang |\<in>|  (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) |`| stateSetFromRuleSet (\<R> i)) \<and> (\<exists> (subforest ) . (tr |\<in>| subforest \<and> subforest |\<subseteq>|  (\<Union>| (childrenSet |`| originalForest)) \<and> subforest \<in> lang)))" by auto
                        qed
                        then show "\<Union>| (childrenSet |`| originalForest) \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) |`| stateSetFromRuleSet (\<R> i))" using biguplusForests_def by blast                            
                      qed
                      show "\<forall>lang. lang |\<in>| \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) |`| stateSetFromRuleSet (\<R> i) \<longrightarrow> (\<exists>subforest. subforest \<in> lang \<and> subforest |\<subseteq>| childrenInTheOriginalForest)"
                      proof
                        show "\<And>lang. lang |\<in>| \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) |`| stateSetFromRuleSet (\<R> i) \<longrightarrow> (\<exists>subforest. subforest \<in> lang \<and> subforest |\<subseteq>| childrenInTheOriginalForest)"
                        proof
                          show "\<And>lang. lang |\<in>| \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) |`| stateSetFromRuleSet (\<R> i) \<Longrightarrow> \<exists>subforest. subforest \<in> lang \<and> subforest |\<subseteq>| childrenInTheOriginalForest"
                          proof -
                            fix lang
                            assume n767987 : " lang |\<in>| \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) |`| stateSetFromRuleSet (\<R> i)"
                              def state == "SOME state . (lang = \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) state \<and> state |\<in>| stateSetFromRuleSet (\<R> i))"
                            then have lang_def : "lang = \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) state \<and> state |\<in>| stateSetFromRuleSet (\<R> i)" using n767987
                              by (smt fimageE someI_ex) 
                            then have "state |\<in>|  \<Union>| (states |`|  (\<R> i))" by (simp add : stateSetFromRuleSet_def)
                            then obtain rule  where n6897 :  "state |\<in>| states rule" and "rule |\<in>|  (\<R> i)" by auto
                                
                            from n7687 have "originalForest \<in> (\<Oplus> ( (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i)) |`| (\<R> i)))" by auto
                            then obtain subforest where nb5456897 : " (subforest \<in> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i)) rule \<and> subforest |\<subseteq>| originalForest)" using bigoplusForests_def
                              by (smt \<open>rule |\<in>| \<R> i\<close> fimage_eqI mem_Collect_eq) 
                            hence "subforest \<in> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i)) rule" by auto
                            then obtain tree where n7656876 : "tree |\<in>| subforest" and "tree_for_rule (\<A> i) rule tree" using forest_language_for_rule_def
                              by (smt mem_Collect_eq) 
                            then obtain child where n6756987 : "child |\<in>| childrenSet tree" and n657987 : "evaluation (\<A> i) child = state" using n6897 tree_for_rule_def
                              by (metis fimageE)
                            then have "child |\<in>| childrenInTheOriginalForest" using childrenInTheOriginalForest_def n7656876 nb5456897
                              using fset_rev_mp by blast
                            from n657987 language_for_state_def have n6587 : "child \<in> \<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> i) state" by (simp add : language_for_state_def)
                            def subforest2 == "(finsert child fempty)"
                            have "subforest2 \<in> lang" using lang_def subforest2_def n6587
                              by (simp add: singletonRuleLang) 
                            have "subforest2 |\<subseteq>| childrenInTheOriginalForest" using subforest2_def  n6756987 n6756987 n7656876 childrenInTheOriginalForest_def
                              using \<open>child |\<in>| childrenInTheOriginalForest\<close> by auto
                            have "subforest2 \<in> lang \<and> subforest2 |\<subseteq>| childrenInTheOriginalForest"
                              by (simp add: \<open>subforest2 \<in> lang\<close> \<open>subforest2 |\<subseteq>| childrenInTheOriginalForest\<close>)  
                            then show "\<exists>subforest. subforest \<in> lang \<and> subforest |\<subseteq>| childrenInTheOriginalForest"  by auto
                            qed
                          qed
                        qed
                  qed
                qed
            qed
          qed
          then show "x \<in> \<Psi>\<^sub>\<phi> ` \<Oplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1 |`| stateSetFromRuleSet (\<R> \<aa>\<^sub>1)) \<and> x \<in> \<Psi>\<^sub>\<phi> ` \<Oplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2 |`| stateSetFromRuleSet (\<R> \<aa>\<^sub>2))" using \<A>.simps
            by metis 
        qed
        from u1 u2 show "x \<in> fset (inf_fset2 (boundedForests n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma> (stateSetFromRuleSet (\<R> \<aa>\<^sub>1)) (stateSetFromRuleSet (\<R> \<aa>\<^sub>2))))" using notin_fset
          by fastforce 
      qed
    qed
  qed
qed
  
lemma pathsTreeForestLang :
  "\<Pi>\<^sub>\<phi> language = \<Pi>\<^sub>\<tau> (\<Union>x\<in>language. fset x)" 
proof (simp add : pathsForForestLanguage_def pathsForTreeLanguage_def pathsInForest_def)
  show "{p. \<exists>t\<in>language. fBex t (\<lambda>x. p |\<in>| \<Pi> x)} = {p. \<exists>y\<in>language. \<exists>t\<in>fset y. p |\<in>| \<Pi> t}"
  proof
    show "{p. \<exists>t\<in>language. fBex t (\<lambda>x. p |\<in>| \<Pi> x)} \<subseteq> {p. \<exists>y\<in>language. \<exists>t\<in>fset y. p |\<in>| \<Pi> t}" by (smt Collect_mono fBexE notin_fset) 
    show "{p. \<exists>y\<in>language. \<exists>t\<in>fset y. p |\<in>| \<Pi> t} \<subseteq> {p. \<exists>t\<in>language. fBex t (\<lambda>x. p |\<in>| \<Pi> x)}" by (smt Collect_mono fBexI notin_fset) 
  qed
qed
  
  
  
  
lemma pathsFactor : 
  assumes "tree |\<in>| forest"
  assumes "forest \<in> language"
  assumes "\<And> forest . forest \<in> language \<Longrightarrow> (\<And>tr . tr \<in> (fset forest) \<Longrightarrow> root tr = \<alpha>)"
  shows "\<alpha> \<bullet> (\<Pi>\<^sub>\<phi> (op \<diamondop> \<alpha> ` language) \<union> {[]}) = \<Pi>\<^sub>\<phi> (language)" 
proof -
  from factorAndPrefix have "\<And>witness trrlanguage.((\<And>tr . tr \<in> trrlanguage \<Longrightarrow> root tr = \<alpha>) \<Longrightarrow>witness \<in> trrlanguage \<Longrightarrow> \<alpha> \<bullet> \<Pi>\<^sub>\<tau> (\<alpha> \<diamondop>\<tau>\<lambda> trrlanguage) \<union> {[\<alpha>]} = \<Pi>\<^sub>\<tau> trrlanguage)" by auto
  def trrlanguage == "\<Union> (fset ` language)"
  hence "tree \<in> trrlanguage" using assms notin_fset  by (metis UN_I) 
  hence "\<alpha> \<bullet> \<Pi>\<^sub>\<tau> (\<alpha> \<diamondop>\<tau>\<lambda> trrlanguage) \<union> {[\<alpha>]} = \<Pi>\<^sub>\<tau> trrlanguage" using assms(2) factorAndPrefix trrlanguage_def UN_I  by (smt Union_iff assms(3) bex_imageD) 
  have n6556877 : "\<And>p t.  (fBex (\<alpha> \<diamondop> t) (\<lambda>x. p |\<in>| \<delta>\<^sub>\<tau> x)) = (\<exists> tree . (tree |\<in>| \<alpha> \<diamondop> t \<and> p |\<in>| \<delta>\<^sub>\<tau> tree))" using fBexE fBexI by auto
  have "\<Pi>\<^sub>\<phi> (op \<diamondop> \<alpha> ` language) = \<Pi>\<^sub>\<tau> (\<alpha> \<diamondop>\<tau>\<lambda> trrlanguage)" 
  proof (simp add : trrlanguage_def pathsForForestLanguage_def pathsForTreeLanguage_def pathsInForest_def factorByRootSymbol_def n6556877 factorByRootSymbolF_lemma(1) factorByRootSymbol_def)
    show "{p. \<exists>t\<in>language. \<exists>tree. (\<exists>treea\<in>fset t. root treea = \<alpha> \<and> tree |\<in>| childrenSet treea) \<and> p |\<in>| \<delta>\<^sub>\<tau> tree} = {p. \<exists>t. (\<exists>y\<in>language. \<exists>tree\<in>fset y. root tree = \<alpha> \<and> t |\<in>| childrenSet tree) \<and> p |\<in>| \<delta>\<^sub>\<tau> t} " by auto
  qed
  have "\<Pi>\<^sub>\<phi> (language) = \<Pi>\<^sub>\<tau> trrlanguage" 
  proof (simp add : trrlanguage_def)
    from pathsTreeForestLang show "\<Pi>\<^sub>\<phi> language = \<Pi>\<^sub>\<tau> (\<Union>x\<in>language. fset x)" by auto
  qed
  show "\<alpha> \<bullet> (\<Pi>\<^sub>\<phi> (op \<diamondop> \<alpha> ` language) \<union> {[]}) = \<Pi>\<^sub>\<phi> (language)"   using \<open>\<Pi>\<^sub>\<phi> (op \<diamondop> \<alpha> ` language) = \<Pi>\<^sub>\<tau> (\<alpha> \<diamondop>\<tau>\<lambda> trrlanguage)\<close> \<open>\<Pi>\<^sub>\<phi> language = \<Pi>\<^sub>\<tau> trrlanguage\<close> \<open>\<alpha> \<bullet> \<Pi>\<^sub>\<tau> (\<alpha> \<diamondop>\<tau>\<lambda> trrlanguage) \<union> {[\<alpha>]} = \<Pi>\<^sub>\<tau> trrlanguage\<close> unionAppend by auto
qed
  
      
    
lemma emptyPathsLanguage :
  assumes "\<And>x . (x \<in> language) \<Longrightarrow> x = {||}"
  shows "(\<Pi>\<^sub>\<phi> (language)) = {}" 
    proof (simp add :pathsForForestLanguage_def)
      from assms have "\<And>x. \<And>t . t\<in>language \<Longrightarrow> x |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> t \<Longrightarrow>  x |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> {||}" by auto
      hence  "\<And>x. \<And>t . t\<in>language \<Longrightarrow> x |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> t \<Longrightarrow>  x |\<in>| {||}" using pathsInForest_def by fastforce
      then show "\<forall>x. \<forall>t\<in>language. x |\<notin>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> t" by auto
    qed
  
      
lemma psiRulesStatesLemma:              
  fixes \<R>
  fixes \<alpha>
  assumes "\<And> \<ii> rule . rule |\<in>| (\<R> \<ii>) \<Longrightarrow> symbol rule = \<alpha>"
  assumes "(\<And>i. \<exists>rule. rule |\<in>| \<R> i)"
  assumes a1 : "\<exists> forest . (forest \<in> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma> (stateSetFromRuleSet (\<R> \<aa>\<^sub>1))   (stateSetFromRuleSet (\<R> \<aa>\<^sub>2)))) \<and> forest \<noteq> fempty)"
    (* assumes a1 : "\<exists> forest. forest \<in> \<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2)) \<and> forest \<noteq> {||}" *)
  shows "\<alpha> \<bullet> (\<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma> (stateSetFromRuleSet (\<R> \<aa>\<^sub>1)) (stateSetFromRuleSet (\<R> \<aa>\<^sub>2)))) \<union> {[]}) =
    \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2) ))"
proof -
  from psiRulesStatesLemma1 assms have n6545765 : " \<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma> (stateSetFromRuleSet (\<R> \<aa>\<^sub>1)) (stateSetFromRuleSet (\<R> \<aa>\<^sub>2))) = op \<diamondop> \<alpha> ` \<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2)) " by auto
  then have "\<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma> (stateSetFromRuleSet (\<R> \<aa>\<^sub>1)) (stateSetFromRuleSet (\<R> \<aa>\<^sub>2)))) = \<Pi>\<^sub>\<phi> (op \<diamondop> \<alpha> ` \<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))) " by auto
  then have n659878 : "\<alpha> \<bullet> (\<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma> (stateSetFromRuleSet (\<R> \<aa>\<^sub>1)) (stateSetFromRuleSet (\<R> \<aa>\<^sub>2)))) \<union> {[]}) = \<alpha> \<bullet> (\<Pi>\<^sub>\<phi> (op \<diamondop> \<alpha> ` \<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))) \<union> {[]})" by auto
  have a2 : "(\<And>forest tr. forest \<in> (\<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))) \<Longrightarrow> tr \<in> fset forest \<Longrightarrow> root tr = \<alpha>)"
  proof -
    fix forest tr
    assume "forest \<in> (\<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2)))"
    hence "forest \<in> (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))"     by (simp add :\<Z>\<^sub>\<phi>\<^sub>F_def)
    then show "tr \<in> fset forest \<Longrightarrow> root tr = \<alpha>" using assms(1) oplusRoots      by blast 
  qed
  from a1 obtain forest where n975653 : "forest \<in> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma> (stateSetFromRuleSet (\<R> \<aa>\<^sub>1))   (stateSetFromRuleSet (\<R> \<aa>\<^sub>2)))) \<and> forest \<noteq> fempty" by auto
  from n6545765 have n76465578 : "(\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma> (stateSetFromRuleSet (\<R> \<aa>\<^sub>1))   (stateSetFromRuleSet (\<R> \<aa>\<^sub>2)))) = op \<diamondop> \<alpha> ` \<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))" by auto
  hence "forest \<in> op \<diamondop> \<alpha> ` \<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))" using n975653 by auto
  then obtain forest2 where n864654 : "forest = \<alpha>  \<diamondop> forest2" and n76454 : "forest2 \<in> \<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))" by auto
  from n975653 have n8764654 :  "forest \<noteq> fempty" by auto
  hence "forest2 \<noteq> fempty" using n864654 factorByRootSymbolF_lemma factorByRootSymbol_def factorByRootSymbolF_def  by (smt bot_fset.rep_eq empty_Collect_eq fempty_iff fset_inverse set_to_fset_def) 
  then have ny5r876 : "forest2 \<in> (\<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))) \<and> forest2 \<noteq> {||}" using n76454 by auto
  then obtain tree where nu6453 :"tree |\<in>| forest2" by auto
  from n8764654 obtain tree2 where n862356 : "tree2 |\<in>| forest" by auto
  from a2 pathsFactor nu6453 ny5r876 have 
    " \<alpha> \<bullet> (\<Pi>\<^sub>\<phi> (op \<diamondop> \<alpha> ` (\<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2)))) \<union> {[]}) = \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2)))"
    by auto
  hence " \<alpha> \<bullet> (\<Pi>\<^sub>\<phi> ((\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma> (stateSetFromRuleSet (\<R> \<aa>\<^sub>1))   (stateSetFromRuleSet (\<R> \<aa>\<^sub>2))))) \<union> {[]}) = \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2)))" using n76465578 by auto
  then show "\<alpha> \<bullet> (\<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma> (stateSetFromRuleSet (\<R> \<aa>\<^sub>1)) (stateSetFromRuleSet (\<R> \<aa>\<^sub>2)))) \<union> {[]}) = \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2)))" by auto
qed
  
  
    
    (* ======================================= MAIN LEMMA =========================================== *)
    
    
  
lemma wMonotonic:
  shows "\<And>i. \<W> n (Suc y) \<R> i |\<subseteq>| \<W> n y \<R> i"
  by (metis \<W>.simps(2) caseDistinction.elims fminus_iff fsubsetI)
    
    
lemma
  assumes "pathFitsListAndListIsARun \<ii> p r"
  assumes "r \<noteq> []"
  shows "hd r |\<in>| rule_set (\<A> \<ii>)"
  by (metis assms(1) assms(2) hd_Cons_tl pathFitsListAndListIsARun.simps(2) pathFitsListAndListIsARun.simps(4))
    
    
    
lemma piUnionLemma:
  fixes n l
  shows " \<Pi>\<^sub>\<tau>\<^sub>F ( \<Union>| (\<Z>\<^sub>\<phi> n l)) = \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n l)"
  by (simp add: aux50)
    

    

  
lemma notation_lemma1 :
  fixes Sa1 Sa2 n
  shows " (\<Pi>\<^sub>\<phi> ((fset (\<Z>\<^sub>\<phi> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2))))) = (\<Pi>\<^sub>\<delta> (fset (\<Z>\<^sub>\<delta> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2))))"
proof -
  from pathsForForestLanguage_def have b1 : " (\<Pi>\<^sub>\<phi> ((fset (\<Z>\<^sub>\<phi> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2))))) = {p . (\<exists> t \<in> ((fset (\<Z>\<^sub>\<phi> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2)))) . p |\<in>| pathsInForest t)}" by auto
  have b2 : "(\<Pi>\<^sub>\<delta> (fset (\<Z>\<^sub>\<delta> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2)))) = \<Union> (fset ` (fset (\<Z>\<^sub>\<delta> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2))))" by auto
  have b3 : "\<Union> (fset ` (fset (\<Z>\<^sub>\<delta> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2)))) = {p . (\<exists> t \<in> (fset (\<Z>\<^sub>\<delta> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2))) . p |\<in>| t)}" by (smt Collect_cong Sup_set_def ffUnion.rep_eq ffUnionI ffUnionLemma mem_Collect_eq notin_fset) 
  have b4 : "\<And>p . (\<exists> t \<in> ((fset (\<Z>\<^sub>\<phi> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2)))) . p |\<in>| pathsInForest t) = (\<exists> t \<in> (fset (\<Z>\<^sub>\<delta> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2))) . p |\<in>| t)" 
  proof -
    fix p
    show "(\<exists> t \<in> ((fset (\<Z>\<^sub>\<phi> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2)))) . p |\<in>| pathsInForest t) = (\<exists> t \<in> (fset (\<Z>\<^sub>\<delta> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2))) . p |\<in>| t)" 
    proof (simp add : \<Z>\<^sub>\<delta>_def \<Z>\<^sub>\<phi>_def)
      show "(\<exists>t\<in>fset (inf_fset2 (boundedForests n) (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2)). p |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> t) = (\<exists>x\<in>fset (inf_fset2 (boundedForests n) {f. \<Pi>\<^sub>\<iota>\<^sub>\<phi> f \<in> \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2}). p |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> x)"
      proof
        have "\<And>t. t \<in> (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2)  \<Longrightarrow> \<Pi>\<^sub>\<iota>\<^sub>\<phi> t \<in> \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2" using psiDeltaPsi by blast
        then have "\<And>t . t\<in>fset (inf_fset2 (boundedForests n) (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2)) \<Longrightarrow> t \<in> fset (inf_fset2 (boundedForests n) {f. \<Pi>\<^sub>\<iota>\<^sub>\<phi> f \<in> \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2})"          using inf_fset2.rep_eq by fastforce
        then show "\<exists>t\<in>fset (inf_fset2 (boundedForests n) (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2)). p |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> t \<Longrightarrow> \<exists>x\<in>fset (inf_fset2 (boundedForests n) {f. \<Pi>\<^sub>\<iota>\<^sub>\<phi> f \<in> \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2}). p |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> x"          by blast
        show "\<exists>x\<in>fset (inf_fset2 (boundedForests n) {f. \<Pi>\<^sub>\<iota>\<^sub>\<phi> f \<in> \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2}). p |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> x \<Longrightarrow> \<exists>t\<in>fset (inf_fset2 (boundedForests n) (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2)). p |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> t" 
        proof (simp add : \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>_def \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta>_def)
          show "\<exists>x\<in>fset (inf_fset2 (boundedForests n) {f. \<Pi>\<^sub>\<iota>\<^sub>\<phi> f \<in> \<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> \<circ> \<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1) |`| Sa1) \<and> \<Pi>\<^sub>\<iota>\<^sub>\<phi> f \<in> \<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> \<circ> \<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2) |`| Sa2)}). p |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> x \<Longrightarrow>
    \<exists>t\<in>fset (inf_fset2 (boundedForests n) (\<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1 |`| Sa1) \<inter> \<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2 |`| Sa2))). p |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> t"
          proof -
            assume "\<exists>x\<in>fset (inf_fset2 (boundedForests n) {f. \<Pi>\<^sub>\<iota>\<^sub>\<phi> f \<in> \<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> \<circ> \<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1) |`| Sa1) \<and> \<Pi>\<^sub>\<iota>\<^sub>\<phi> f \<in> \<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> \<circ> \<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2) |`| Sa2)}). p |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> x"
            then obtain x where y1 : "x |\<in>| boundedForests n" and y2 : "\<Pi>\<^sub>\<iota>\<^sub>\<phi> x \<in> \<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> \<circ> \<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1) |`| Sa1)" and y3 : "\<Pi>\<^sub>\<iota>\<^sub>\<phi> x \<in> \<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> \<circ> \<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2) |`| Sa2)" and y4 : "p |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> x"                by (metis (mono_tags, lifting) IntD2 finterD1 inf_fset2.rep_eq mem_Collect_eq notin_fset) 
                
            from y2  have "\<Pi>\<^sub>\<iota>\<^sub>\<phi> x \<in> \<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| ( \<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1 |`| Sa1))" by auto
            hence "\<Pi>\<^sub>\<iota>\<^sub>\<phi> x \<in> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Psi>\<^sub>\<phi> ` \<Uplus> ( \<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1 |`| Sa1))" using nu67543433 by blast
            then obtain oldPsi1 where y12 : "\<Pi>\<^sub>\<iota>\<^sub>\<phi> x = \<Pi>\<^sub>\<iota>\<^sub>\<phi> oldPsi1" and y10 : "oldPsi1 \<in> (\<Psi>\<^sub>\<phi> ` \<Uplus> ( \<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1 |`| Sa1))" by auto
            from y3  have "\<Pi>\<^sub>\<iota>\<^sub>\<phi> x \<in> \<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| ( \<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2 |`| Sa2))" by auto
            hence "\<Pi>\<^sub>\<iota>\<^sub>\<phi> x \<in> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Psi>\<^sub>\<phi> ` \<Uplus> ( \<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2 |`| Sa2))" using nu67543433 by blast
            then obtain oldPsi2 where y13 : "\<Pi>\<^sub>\<iota>\<^sub>\<phi> x = \<Pi>\<^sub>\<iota>\<^sub>\<phi> oldPsi2" and y11 : "oldPsi2 \<in> (\<Psi>\<^sub>\<phi> ` \<Uplus> ( \<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2 |`| Sa2))" by auto
            from y10 y11 y12 y13 psiOnlyDependsOnPath have n764543 : "oldPsi1 = oldPsi2"                  by (metis imageE psiOnlyDependsOnPath1) 
            from y12  y1 heightBoundedPaths have "oldPsi1 |\<in>| boundedForests n" by blast
            from y10 n764543 y11 have "oldPsi1 \<in> (\<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1 |`| Sa1)) \<inter> (\<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2 |`| Sa2))" by blast
            from y4  y12   have "p |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> oldPsi1" by auto
            have " oldPsi1\<in>fset (inf_fset2 (boundedForests n) (\<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1 |`| Sa1) \<inter> \<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2 |`| Sa2))) \<and> p |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> oldPsi1"                      by (metis (no_types, lifting) \<open>oldPsi1 \<in> \<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1 |`| Sa1) \<inter> \<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2 |`| Sa2)\<close> \<open>oldPsi1 |\<in>| boundedForests n\<close> \<open>p |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> oldPsi1\<close> finterI n764543 notin_fset) 
            then show " \<exists>t\<in>fset (inf_fset2 (boundedForests n) (\<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1 |`| Sa1) \<inter> \<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2 |`| Sa2))). p |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> t" by auto
          qed
        qed
      qed
    qed
  qed
  from b1  b3 b4 show " (\<Pi>\<^sub>\<phi> ((fset (\<Z>\<^sub>\<phi> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2))))) = (\<Pi>\<^sub>\<delta> (fset (\<Z>\<^sub>\<delta> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2))))" by auto
qed
  
  
  
definition rootNode where "rootNode tree = (SOME node . up node = PLACEHOLDER \<and> down node = tree )"  
  
  
lemma hasRoot:
  fixes tree
  shows "up (rootNode tree) = PLACEHOLDER \<and> down (rootNode tree) = tree"
  by (metis (mono_tags, lifting) node.select_convs(1) node.select_convs(2) node.surjective rootNode_def someI)
    
lemma hasRoot2:
  fixes tree
  shows "isNodeIn (rootNode tree) tree \<and> isRootNode (rootNode tree)"
  by (simp add: hasRoot isNodeIn_def isRootNode_def)
    
    
fun nodeListForPath :: "abc list \<Rightarrow> abc tree \<Rightarrow> abc node list" where
  "nodeListForPath [] tr = []"
| "nodeListForPath [a] tr = [rootNode tr]" 
| "nodeListForPath (a#(b#c)) tr = (rootNode tr)#(nodeListForPath (b#c) (SOME x. (x |\<in>| childrenSet tr \<and> (b#c) |\<in>| \<Pi> x) ))" 
  
fun nodeListFitsPath :: "abc list \<Rightarrow> abc node list \<Rightarrow> bool" where
  "nodeListFitsPath [] [] = True"
| "nodeListFitsPath (a#b) (c#d) = ((a = root ((down c))) \<and> nodeListFitsPath b d)"
| "nodeListFitsPath [] (c#d) = False"
| "nodeListFitsPath (a#b) [] = False"
  
lemma childPath :
  assumes a1: "p |\<in>| \<delta>\<^sub>\<tau> (NODE parent children)"
  shows "p = [parent] \<or> (\<exists>child.(\<exists>childPath.(child |\<in>| children \<and> p = parent#childPath \<and> childPath |\<in>| \<Pi> child)))"
  using assms by auto
    
    
lemma zInP :
  assumes "tr |\<in>| \<ff> (n) \<R>"
  shows "tr \<in> \<P> \<R>"
  using  \<ff>_def
  by (metis assms(1)  zIntersectLemma) 
    
    
lemma pRoot : 
  assumes "\<And> \<ii> rule .(rule |\<in>| \<R> \<ii> \<Longrightarrow> symbol rule = \<alpha>)"
  assumes "tr \<in> \<P> \<R>"
  shows "root tr = \<alpha>"  
  using \<P>_def satisfiesApproximatorForRuleSet_def pathSatisfiesApproximatorForRuleSet_def pathsInTree_def
proof -
  obtain nns :: "abc tree \<Rightarrow> abc node list" and nn :: "abc tree \<Rightarrow> abc node" where
    f1: "isAPathp (nns tr) \<and> nns tr = [nn tr] \<and> down (nn tr) = tr \<and> nns tr \<in> pathsInTree tr"
    using theSingletonPathExists by moura
  then have f2: "pathSatisfiesApproximatorForRuleSet [nn tr] (\<R> elem_11) elem_11"
    using \<P>_def assms(2) satisfiesApproximatorForRuleSet_def by force
  obtain rrs :: "ot \<Rightarrow> (stt, abc) rule fset \<Rightarrow> abc node list \<Rightarrow> (stt, abc) rule list" where
    "\<forall>x0 x1 x2. (\<exists>v3. hd v3 |\<in>| x1 \<and> pathFitsListAndListIsARun x0 x2 v3) = (hd (rrs x0 x1 x2) |\<in>| x1 \<and> pathFitsListAndListIsARun x0 x2 (rrs x0 x1 x2))"
    by moura
  then have f3: "(\<not> pathSatisfiesApproximatorForRuleSet [nn tr] (\<R> elem_11) elem_11 \<or> hd (rrs elem_11 (\<R> elem_11) [nn tr]) |\<in>| \<R> elem_11 \<and> pathFitsListAndListIsARun elem_11 [nn tr] (rrs elem_11 (\<R> elem_11) [nn tr])) \<and> (pathSatisfiesApproximatorForRuleSet [nn tr] (\<R> elem_11) elem_11 \<or> (\<forall>rs. hd rs |\<notin>| \<R> elem_11 \<or> \<not> pathFitsListAndListIsARun elem_11 [nn tr] rs))"
    using pathSatisfiesApproximatorForRuleSet_def by auto
  then have "pathFitsListAndListIsARun elem_11 [nn tr] (hd (rrs elem_11 (\<R> elem_11) [nn tr]) # tl (rrs elem_11 (\<R> elem_11) [nn tr]))"
    using f2 by (metis (no_types) hd_Cons_tl nonMatching)
  then show ?thesis
    using f3 f2 f1 by (metis (no_types) assms(1) labelOfNode_def pathFitsListAndListIsARun.simps(2))
qed
  
  
lemma fRoot :
  assumes "\<And> \<ii> rule . rule |\<in>| \<R> \<ii> \<Longrightarrow> symbol rule = \<alpha>"
  assumes "tr |\<in>| \<ff> (n) \<R>"
  shows "root tr = \<alpha>"
  using pRoot \<ff>_def
  by (metis assms(1) assms(2) zInP)
    
    
    (* To each path (as a sequence of symbols) corresponds a sequence of nodes *)
lemma nodeListForPathExists :
  fixes tr
  shows "\<And>p . p |\<in>| \<Pi> tr \<Longrightarrow> (nodeListFitsPath p (nodeListForPath p tr) \<and> (nodeListForPath p tr) \<in> (pathsInTree tr))"
proof (induct tr)
  fix parent children p
  assume a4 : "(\<And>x2aa p. x2aa \<in> fset children \<Longrightarrow> p |\<in>| \<delta>\<^sub>\<tau> x2aa \<Longrightarrow> (nodeListFitsPath p (nodeListForPath p x2aa) \<and> nodeListForPath p x2aa \<in> pathsInTree x2aa))"
  assume m1 : "p |\<in>| \<delta>\<^sub>\<tau> (NODE parent children)"
  from m1 have a9 : "p |\<in>| fimage (append [parent]) ((\<Union>| (fimage \<Pi> children)) |\<union>|  (finsert [] {||}))" by auto
  then obtain tail where n570 : "p = parent#tail" and n571 : "tail |\<in>| ((\<Union>| (fimage \<Pi> children)) |\<union>|  (finsert [] {||}))"          using childPath m1 by blast 
  show "(nodeListFitsPath p (nodeListForPath p (NODE parent children)) \<and> nodeListForPath p (NODE parent children) \<in> pathsInTree (NODE parent children))"
  proof (rule disjE)
    show "tail = [] \<or> tail \<noteq> []" by auto
    show "tail = [] \<Longrightarrow> (nodeListFitsPath p (nodeListForPath p (NODE parent children)) \<and> nodeListForPath p (NODE parent children) \<in> pathsInTree (NODE parent children))"          by (simp add: hasRoot isAPathp.intros(1) n570 pathsInTree_def)
    show "tail \<noteq> [] \<Longrightarrow> (nodeListFitsPath p (nodeListForPath p (NODE parent children)) \<and> nodeListForPath p (NODE parent children) \<in> pathsInTree (NODE parent children))"
    proof 
      assume n658 : "tail \<noteq> []"
      from a9 n658 n570 n571 obtain child childPath where a1 : "child |\<in>| children" and a2 : "p = parent#childPath" and a3 : "childPath |\<in>| \<Pi> child"      by auto
      from a2 n570 have n572 : "childPath = tail" by auto
      then obtain tail1 tail2 where n578 : "childPath = tail1#tail2" using n658              using a3 noEmptyPathsInPi by blast 
      from a1 a2 a3 a4 have q1 : "nodeListFitsPath childPath (nodeListForPath childPath child)" by (meson notin_fset) 
      have "parent = root (down (rootNode (NODE parent children)))" by (simp add: hasRoot)
      have n1 : "nodeListForPath (parent#(tail1#tail2)) (NODE parent children) = (nodeListForPath (parent#(tail1#tail2)) (NODE parent children))" by auto
      have n2 : "(\<And> P. \<And>tr. (parent#(tail1#tail2)) = [] \<Longrightarrow> (NODE parent children) = tr \<Longrightarrow> (nodeListForPath (parent#(tail1#tail2)) (NODE parent children)) = [] \<Longrightarrow> P)" by auto
      have n3 : " \<And>P.  (\<And>a tr. (parent#(tail1#tail2)) = [a] \<Longrightarrow> (NODE parent children) = tr \<Longrightarrow> (nodeListForPath (parent#(tail1#tail2)) (NODE parent children)) = [rootNode tr] \<Longrightarrow> P)" by auto
      from n1 n2 n3 nodeListForPath.elims   have n4 : "(\<And>a b c tr. (parent#(tail1#tail2)) = a # b # c \<Longrightarrow> (NODE parent children) = tr \<Longrightarrow> (nodeListForPath (parent#(tail1#tail2)) (NODE parent children)) = rootNode tr # nodeListForPath (b # c) (SOME x. x |\<in>| childrenSet tr \<and> b # c |\<in>| \<delta>\<^sub>\<tau> x))" by auto
      then  have p1 : "(nodeListForPath (parent#(tail1#tail2)) (NODE parent children)) = (rootNode (NODE parent children))#(nodeListForPath (tail1#tail2) (SOME x. (x |\<in>| childrenSet (NODE parent children) \<and> (tail1#tail2) |\<in>| \<Pi> x) ))"      by simp 
      then            have   "(nodeListForPath (parent#childPath) (NODE parent children)) = (rootNode (NODE parent children))#(nodeListForPath childPath (SOME x. (x |\<in>| childrenSet (NODE parent children) \<and> childPath |\<in>| \<Pi> x) ))"       using n578 by auto 
      then have a14 : "(nodeListForPath p (NODE parent children)) = (rootNode (NODE parent children))#(nodeListForPath childPath (SOME x. (x |\<in>| childrenSet (NODE parent children) \<and> childPath |\<in>| \<Pi> x) ))" using a2 by auto
      def child2 == "(SOME x. (x |\<in>| childrenSet (NODE parent children) \<and> childPath |\<in>| \<Pi> x))"
      from a1 have a11 : "child |\<in>| childrenSet (NODE parent children)" by auto
      have a12 : "(child2 |\<in>| childrenSet (NODE parent children) \<and> childPath |\<in>| \<Pi> child2)" using child2_def a11 a3 by (metis (mono_tags, lifting) childrenSet.simps someI_ex)
      from a4 a12 have a13 : "nodeListFitsPath childPath (nodeListForPath childPath child2)" using childrenSet.simps notin_fset by fastforce
      from a13 have "((parent = root ((down (rootNode (NODE parent children))))) \<and> nodeListFitsPath childPath (nodeListForPath childPath child2))" by (simp add: \<open>parent = root (down (rootNode (NODE parent children)))\<close>)
      then show "nodeListFitsPath p (nodeListForPath p (NODE parent children))" using a2 nodeListFitsPath.simps a14 using child2_def by auto 
      from a1 a2 a3 a4 have q2 : "(nodeListForPath childPath child) \<in> pathsInTree child" by (meson notin_fset)
      then have b6756 : "isAPathp (nodeListForPath childPath child)" using pathsInTree_def by blast
      obtain e1 e2 where b10 : "e1#e2 =(nodeListForPath childPath child2)"        by (metis (mono_tags, lifting) a12 a4 childrenSet.simps noEmptyPathsInTree nodeListForPath.elims notin_fset)
      then   have b11 : "down e1 = child2"     by (metis (no_types, lifting) hasRoot list.distinct(1) list.sel(1) nodeListForPath.elims)
      from b10 b11 a12 have "(\<exists>e1.\<exists>tail.((nodeListForPath childPath child2) = (e1#tail)) \<and> (immediatelyDominates (rootNode (NODE parent children)) e1))"    by (metis hasRoot immediatelyDominates_def) 
      then have e1 :  "(isAPathp (nodeListForPath p (NODE parent children)))" using a14 b6756 isAPathp.simps    by (smt a12 a4 child2_def childrenSet.simps hasRoot immediatelyDominates_def mem_Collect_eq notin_fset pathsInTree_def)
      from down_def hasRoot  have n765 : "down (rootNode (NODE parent children)) = (NODE parent children)" by blast
      from a14 n765 have e2 : " (( \<exists>e1.\<exists>tail.((nodeListForPath p (NODE parent children)) = (e1#tail) \<and> down e1 = (NODE parent children))))" by blast
      from e1 e2 pathsInTree_def show "nodeListForPath p (NODE parent children) \<in> pathsInTree (NODE parent children)" by auto
    qed
  qed
qed
  
  
lemma nodeListFitsTree :
  fixes tr
  shows "\<And>p . p |\<in>| \<Pi> tr \<Longrightarrow> (nodeListForPath p tr) \<in> (pathsInTree tr)"
  using nodeListForPathExists by auto
    
    
definition RByCase where
  "RByCase \<ii> a b \<ii>2 = caseDistinction (\<ii> = \<ii>2) a b"
  
  
  
  
  (* =================================================== *)
  
  (* Here, the goal is to show the difficult direction for depth < N *)
  
lemma existsWitnessTree2 :
  fixes \<ii> tr
  shows "\<And>p   . \<And> nodeList . \<And> run. 
           nodeList \<noteq> [] \<Longrightarrow>
           down (hd nodeList) = tr \<Longrightarrow> 
           isAPathp nodeList 
 \<Longrightarrow> (pathFitsListAndListIsARun \<ii> nodeList run)
 \<Longrightarrow> nodeListFitsPath p nodeList           
\<Longrightarrow> height tr \<le> \<N>
 \<Longrightarrow> \<exists> witness . 
 (witness \<in> ((((((\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>))  (hd run))))))
  \<and> \<delta>\<^sub>\<tau> witness |\<subseteq>| \<delta>\<^sub>\<tau> tr
  \<and> p |\<in>| \<delta>\<^sub>\<tau> witness)"
proof (induct tr)
  show "\<And>x1a x2a p nodeList run.
       (\<And>x2aa p nodeList run.
           x2aa \<in> fset x2a \<Longrightarrow>
           nodeList \<noteq> [] \<Longrightarrow>
           down (hd nodeList) = x2aa \<Longrightarrow> 
           isAPathp nodeList \<Longrightarrow>
           pathFitsListAndListIsARun \<ii> nodeList run \<Longrightarrow>
           nodeListFitsPath p nodeList \<Longrightarrow>
           height x2aa \<le> \<N> ==>
           \<exists>witness. witness \<in>   (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>)  (hd ( run)) ) \<and> \<delta>\<^sub>\<tau> witness |\<subseteq>| \<delta>\<^sub>\<tau> x2aa \<and> p |\<in>| \<delta>\<^sub>\<tau> witness) \<Longrightarrow>
       nodeList \<noteq> [] \<Longrightarrow>
       down (hd nodeList) = (NODE x1a x2a) \<Longrightarrow> 
       isAPathp nodeList \<Longrightarrow>
       pathFitsListAndListIsARun \<ii> nodeList run \<Longrightarrow>
       nodeListFitsPath p nodeList \<Longrightarrow>
height (NODE x1a x2a) \<le> \<N> \<Longrightarrow>
       \<exists>witness. witness \<in>   (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) (hd ( run))) \<and> \<delta>\<^sub>\<tau> witness |\<subseteq>| \<delta>\<^sub>\<tau> (NODE x1a x2a) \<and> p |\<in>| \<delta>\<^sub>\<tau> witness"
  proof -
    fix parent children p  run
    fix nodeList :: "(abc node list)"
    assume a1 : "(\<And>x2aa p nodeList run.
           x2aa \<in> fset children \<Longrightarrow>
            nodeList \<noteq> [] \<Longrightarrow>
           down (hd nodeList) = x2aa \<Longrightarrow> 
           isAPathp nodeList \<Longrightarrow>
           pathFitsListAndListIsARun \<ii> nodeList run \<Longrightarrow>
           nodeListFitsPath p nodeList \<Longrightarrow>
height x2aa \<le> \<N> \<Longrightarrow>
           \<exists>witness. witness \<in>  (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>)  (hd ( run))) \<and>  \<delta>\<^sub>\<tau> witness |\<subseteq>| \<delta>\<^sub>\<tau> x2aa \<and> p |\<in>|  \<delta>\<^sub>\<tau> witness)"
    assume a100 : "nodeList \<noteq> []"
    assume a2 : "down (hd nodeList) = (NODE parent children)"
    assume a2b : "isAPathp nodeList"
    assume a3 : "pathFitsListAndListIsARun \<ii> nodeList run"
    assume a4 : "nodeListFitsPath p nodeList"
    assume a67 : "height (NODE parent children) \<le> \<N>"
      
      
    def nodesTail == "tl nodeList"
    obtain nodesRoot where b100 : "nodeList = nodesRoot#nodesTail" using a2b isAPathp.simps by (metis a100 list.collapse nodesTail_def tl_Nil)  
    from b100 have v100 :  "nodesRoot = hd nodeList" by auto
    obtain runHead runTail where b109 : "run = runHead#runTail"
      by (metis a3 b100 hd_Cons_tl pathFitsListAndListIsARun.simps(3)) 
    obtain pHead pTail where b101 : "p = pHead#pTail"
      using a4 b100 nodeListFitsPath.elims(2) by blast
    from a100 nodesTail_def  have b102 : "nodeList \<noteq> []" by simp
    def child2 == "(( (down (hd nodesTail))))"
    have b103 : "nodesTail \<noteq> [] \<Longrightarrow> child2 \<in> fset children"
    proof -
      from a2 v100 a2b isAPath.simps b100  have "nodesTail \<noteq> [] \<Longrightarrow>(immediatelyDominates nodesRoot (hd nodesTail))"        by (metis isAPathp.simps list.sel(1) list.sel(3)) 
      then have "nodesTail \<noteq> [] \<Longrightarrow> ((down (hd nodesTail)) |\<in>| (childrenSet (down nodesRoot)))" using immediatelyDominates_def by auto
      then show "nodesTail \<noteq> [] \<Longrightarrow> child2 \<in> fset children" using child2_def a2 b100 using childrenSet.simps list.sel(1) notin_fset by force 
    qed
    have b104 : "down (hd nodesTail) = child2" using child2_def by auto 
    from a2b nodesTail_def have b104a : "nodesTail \<noteq> [] \<Longrightarrow> isAPathp nodesTail"       by (metis isAPathp.simps list.sel(3))   (* not actually true, since the first element is not a root. have to relax this and define something that only requires immediatelyDominates *)
    have b105 : "pathFitsListAndListIsARun \<ii> nodesTail runTail" using a3 b100 b109 pathFitsListAndListIsARun.simps by simp
    have b106 : "nodeListFitsPath pTail nodesTail" using a4 b100 b101 nodeListFitsPath.simps(2) by simp
    from a67 b103 have b1156 : "nodesTail \<noteq> [] \<Longrightarrow> height child2 \<le> \<N>" using childDepth      by (meson dual_order.trans less_imp_le_nat notin_fset) 
    from a1 b103 b104 b104a b105 b106 b1156 obtain downWitness where b120 :
      "nodesTail \<noteq> [] \<Longrightarrow> downWitness \<in>   (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>)  (hd ( runTail))) \<and> \<delta>\<^sub>\<tau> downWitness |\<subseteq>| \<delta>\<^sub>\<tau> child2 \<and> pTail |\<in>| \<delta>\<^sub>\<tau> downWitness" by blast
    from pathFitsListAndListIsARun.simps(2) a3 b100 b109 have  b110 : "(( (labelOfNode nodesRoot = symbol runHead)
                                      \<and> (runHead |\<in>| rule_set (\<A> \<ii>))
                                      \<and> (( (down nodesRoot)) \<in> ( \<V>\<^sub>\<tau> \<ii> runHead  )   )    )
                                      \<and> (pathFitsListAndListIsARun \<ii> nodesTail runTail)
                                      \<and> (\<forall> h.\<forall> t.(runTail = (h#t) \<longrightarrow>  (        (((transition (\<A> \<ii>) (states h) (symbol h) )  |\<in>| states runHead) )        )))        
                                      )"  by metis
    from \<V>\<^sub>\<tau>_def b110 have b111 : "(root (down nodesRoot) = (symbol runHead))" and b112 : "\<Pi> (down nodesRoot) \<in> ((upwardClosure (image \<Pi> (((Z \<N> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) runHead)))))) 
                                 \<union> (image \<Pi> {t . height t > \<N>})) 
                              \<inter> (\<Inter>I \<in> (necess (\<A> \<ii>) \<I> runHead) . (image \<Pi> (existential_satisfaction_set I)   ))" by auto
    from b112 have b113 : "\<Pi> (down nodesRoot) \<in> ((upwardClosure (image \<Pi> (((Z \<N> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) runHead)))))) 
                                 \<union> (image \<Pi> {t . height t > \<N>}))" by auto
    from a2 b100 have "down nodesRoot = (NODE parent children)" by auto
    then have b114 : "height (down nodesRoot) \<le> \<N>" using  a67 by simp
    then have "(down nodesRoot) \<notin> ({t . height t > \<N>})" by auto
    then  have b643 : "\<Pi> (down nodesRoot) \<notin> (image \<Pi> {t . height t > \<N>})" using heightOnlyDependsOnPaths        by auto 
    from b113 b643 have b115 : "\<Pi> (down nodesRoot) \<in> ((upwardClosure (image \<Pi> (((Z \<N> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) runHead)))))))" by blast
    then obtain mirrorPaths where b115a : "mirrorPaths \<in> (image \<Pi> (((Z \<N> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) runHead))))) \<and> fset (\<Pi> (down nodesRoot)) \<supseteq> fset mirrorPaths" using upwardClosure_def by (smt mem_Collect_eq)  
    from b115a obtain mirror where b116 : "\<Pi> mirror |\<subseteq>| \<Pi> (down nodesRoot)" and b117 : "mirror \<in> (Z \<N> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) runHead))" by (metis imageE less_eq_fset.rep_eq)
    from b110 have b130 : "labelOfNode nodesRoot = symbol runHead" by auto
    from b117 Z_def have b131 : "mirror \<in> ((\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) runHead))" by auto
    from b130 b131 have "labelOfNode nodesRoot = root mirror" by (simp add: language_for_rule_def mem_Collect_eq tree_for_rule_def) 
    def newWitness == "NODE parent (finsert downWitness  (childrenSet mirror) ) "
    have "nodesTail \<noteq> [] \<Longrightarrow>newWitness \<in>  (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>)  runHead )"
    proof -
      from  b117  have "mirror \<in> (Z \<N> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) runHead))" by auto
      then have "mirror \<in> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) runHead)" by (simp add: Z_def mem_Collect_eq) 
      from b120 have "nodesTail \<noteq> [] \<Longrightarrow>downWitness \<in>  \<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) (hd ( runTail))" by auto
      obtain h t where y100 : "nodesTail \<noteq> [] \<Longrightarrow>runTail = (h#t)" by (metis b102 b110 list.exhaust pathFitsListAndListIsARun.simps(3)) 
      then have "nodesTail \<noteq> [] \<Longrightarrow>(        (((transition (\<A> \<ii>) (states h) (symbol h) )  |\<in>| states runHead) )        )" using b110 by auto
      have c1 : "nodesTail \<noteq> [] \<Longrightarrow>((root newWitness = symbol runHead))"
      proof -
        from newWitness_def have r3 : "root newWitness = parent" by (simp add: root.simps)
        from a2 have r1 : "down (hd nodeList) = (NODE parent children)" by auto
        from a3 have r2 : "pathFitsListAndListIsARun \<ii> nodeList run" by auto
        from a3 pathFitsListAndListIsARun.simps b100 b109 have r4 : "(labelOfNode (hd nodeList) = symbol runHead)" by auto
        from r3 r1 labelOfNode_def show "root newWitness = symbol runHead" by (metis r4 root.simps)
      qed
      have c2 : "nodesTail \<noteq> [] \<Longrightarrow>((fimage (((evaluation (\<A> \<ii>)))) (childrenSet newWitness)) = states (runHead))"
      proof -
        from b117 Z_def have "mirror \<in> ((\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) runHead))" by auto
        from b131 have b399 : "((fimage (((evaluation (\<A> \<ii>)))) (childrenSet mirror)) = states (runHead))" by (simp add: language_for_rule_def mem_Collect_eq tree_for_rule_def)
        from b120 have b400 : "nodesTail \<noteq> [] \<Longrightarrow>downWitness \<in>   (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>)  (hd ( runTail)))" by auto
        from a3 pathFitsListAndListIsARun.simps b100 b109 
        have b401 : "(\<forall> h.\<forall> t.(runTail = (h#t) \<longrightarrow>  (        (((transition (\<A> \<ii>) (states h) (symbol h) )  |\<in>| states runHead) )        ))) " by simp 
        then have b402  : "nodesTail \<noteq> [] \<Longrightarrow>(        (((transition (\<A> \<ii>) (states (hd ( runTail))) (symbol (hd ( runTail))) )  |\<in>| states ( ( runHead))) )        )"   using y100 by simp
        from b400 have b403 : "nodesTail \<noteq> [] \<Longrightarrow>(root downWitness) = (symbol (hd ( runTail)))" by (simp add: language_for_rule_def mem_Collect_eq tree_for_rule_def)
        from b400 have b404 : "nodesTail \<noteq> [] \<Longrightarrow>(states (hd ( runTail))) = (fimage (evaluation (\<A> \<ii>)) (childrenSet downWitness ))" by (simp add: language_for_rule_def mem_Collect_eq tree_for_rule_def)
        from b402 b403 b404 have "nodesTail \<noteq> [] \<Longrightarrow>(((transition (\<A> \<ii>)) (fimage (evaluation (\<A> \<ii>)) (childrenSet downWitness ))) (root downWitness)) |\<in>| states (runHead)" by simp
        then have b405 : "nodesTail \<noteq> [] \<Longrightarrow>evaluation (\<A> \<ii>) downWitness |\<in>| states (runHead)" using evaluation_def \<Pi>.simps childrenSet.simps evaluation.simps root.simps
          by (metis childrenSet.cases) 
        from b399 b405 newWitness_def show "nodesTail \<noteq> [] \<Longrightarrow>((fimage (((evaluation (\<A> \<ii>)))) (childrenSet newWitness)) = states (runHead))" using childrenSet.simps fimageE fimage_finsert finsert_fimage by auto 
      qed
      from c1 c2 have "nodesTail \<noteq> [] \<Longrightarrow> ((root newWitness = symbol runHead) \<and> ((fimage (((evaluation (\<A> \<ii>)))) (childrenSet newWitness)) = states (runHead)))" by auto
      then have "nodesTail \<noteq> [] \<Longrightarrow>(tree_for_rule (\<A> \<ii>) runHead newWitness)" using tree_for_rule_def by auto
      then show "nodesTail \<noteq> [] \<Longrightarrow>newWitness \<in>  (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>)  runHead )" by (simp add: language_for_rule_def)
    qed
    have "nodesTail \<noteq> [] \<Longrightarrow> \<delta>\<^sub>\<tau> newWitness |\<subseteq>| \<delta>\<^sub>\<tau> (NODE parent children)"
    proof -
      have b130 : "\<delta>\<^sub>\<tau> newWitness = fimage (append [parent]) ((\<Union>| (fimage \<Pi> (finsert downWitness  (childrenSet mirror) ))) |\<union>|  (finsert [] {||})) " by (simp add: newWitness_def)
      have b131 : "\<delta>\<^sub>\<tau> (NODE parent children) = fimage (append [parent]) ((\<Union>| (fimage \<Pi> children)) |\<union>|  (finsert [] {||}))" by (simp add: newWitness_def)
      from b120 have b500 : "nodesTail \<noteq> [] \<Longrightarrow> \<delta>\<^sub>\<tau> downWitness |\<subseteq>| \<delta>\<^sub>\<tau> child2" by auto
      from b103 b500 have b118 : "nodesTail \<noteq> [] \<Longrightarrow> \<delta>\<^sub>\<tau> downWitness |\<subseteq>| (\<Union>| (fimage \<Pi> children))" by (metis ffUnion_upper fimage_eqI inf.orderE le_infI2 notin_fset)
      from b116 have  "\<Pi> mirror |\<subseteq>| \<Pi> (down nodesRoot)" by auto
      have b117 : "\<And> mirrorChild . mirrorChild |\<in>|  (childrenSet mirror) \<Longrightarrow> (\<delta>\<^sub>\<tau>  mirrorChild) |\<subseteq>| (\<Union>| (fimage \<Pi> children)) |\<union>|  (finsert [] {||})"
      proof -
        fix mirrorChild
        assume "mirrorChild |\<in>|  (childrenSet mirror)"
        show "(\<delta>\<^sub>\<tau>  mirrorChild) |\<subseteq>| (\<Union>| (fimage \<Pi> children)) |\<union>|  (finsert [] {||})"
        proof
          fix q
          assume "q |\<in>| (\<delta>\<^sub>\<tau>  mirrorChild)"
          then have "(root mirror)#q |\<in>| \<Pi> mirror" using \<Pi>.simps \<open>mirrorChild |\<in>| childrenSet mirror\<close> childrenSet.simps paths_def root.simps            by (metis root.elims) 
          then have "(root mirror)#q |\<in>| \<Pi> (down nodesRoot)" using b116 by auto
          then have "q \<noteq> [] \<Longrightarrow> \<exists> nchild . nchild |\<in>| childrenSet (down nodesRoot) \<and> q |\<in>| \<Pi> nchild" using pathsOfChildren list.exhaust            by (smt list.inject) 
          then show "q |\<in>| \<Union>| (\<delta>\<^sub>\<tau> |`| children) |\<union>|  (finsert [] {||})" using a2 b100 by auto 
        qed
      qed
      from b117 b118  have b119 : "nodesTail \<noteq> [] \<Longrightarrow> (\<Union>| (fimage \<Pi> (finsert downWitness  (childrenSet mirror) )))|\<subseteq>| (\<Union>| (fimage \<Pi> children)) |\<union>|  (finsert [] {||})" 
        using fPowI ffUnion_Pow_eq ffUnion_mono fimage_fsubsetI finsertE        by (smt ffUnionI finsert_absorb fsubset_finsert funion_finsert_right sup_bot.right_neutral) 
      from b130 b131 show "nodesTail \<noteq> [] \<Longrightarrow> \<delta>\<^sub>\<tau> newWitness |\<subseteq>| \<delta>\<^sub>\<tau> (NODE parent children)" using fimage_mono 
      proof -
        assume "nodesTail \<noteq> []"
        hence b130i : "(\<Union>| (fimage \<Pi> (finsert downWitness  (childrenSet mirror) )))|\<subseteq>| (\<Union>| (fimage \<Pi> children)) |\<union>|  (finsert [] {||})" using b119 by auto
        then have b130l : "fimage (append [parent]) ((\<Union>| (fimage \<Pi> (finsert downWitness  (childrenSet mirror) ))) |\<union>|  (finsert [] {||})) |\<subseteq>| fimage (append [parent]) ((\<Union>| (fimage \<Pi> children)) |\<union>|  (finsert [] {||}))" by auto
        from b130 have b130h : "\<delta>\<^sub>\<tau> newWitness = fimage (append [parent]) ((\<Union>| (fimage \<Pi> (finsert downWitness  (childrenSet mirror) ))) |\<union>|  (finsert [] {||})) " by auto
        hence "\<delta>\<^sub>\<tau> newWitness |\<subseteq>| fimage (append [parent]) ((\<Union>| (fimage \<Pi> children)) |\<union>|  (finsert [] {||}))"          using b130l by auto 
        then show "\<delta>\<^sub>\<tau> newWitness |\<subseteq>| \<delta>\<^sub>\<tau> (NODE parent children)" using \<Pi>.simps by auto
      qed
    qed
    have " nodesTail \<noteq> [] \<Longrightarrow>p |\<in>| \<delta>\<^sub>\<tau> newWitness" using a2 a4 b100 b101 b120 newWitness_def by auto 
    have " nodesTail \<noteq> [] \<Longrightarrow> (newWitness \<in>  (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>)  runHead) \<and> \<delta>\<^sub>\<tau> newWitness |\<subseteq>| \<delta>\<^sub>\<tau> (NODE parent children) \<and> p |\<in>| \<delta>\<^sub>\<tau> newWitness)" using 
        \<open>nodesTail \<noteq> [] \<Longrightarrow> \<delta>\<^sub>\<tau> newWitness |\<subseteq>| \<delta>\<^sub>\<tau> (NODE parent children)\<close> \<open> nodesTail \<noteq> [] \<Longrightarrow>newWitness \<in> \<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) runHead\<close> \<open> nodesTail \<noteq> [] \<Longrightarrow>p |\<in>| \<delta>\<^sub>\<tau> newWitness\<close> by auto 
    then have k99 : " nodesTail \<noteq> [] \<Longrightarrow> \<exists>witness. witness \<in> \<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) (hd run) \<and> \<delta>\<^sub>\<tau> witness |\<subseteq>| \<delta>\<^sub>\<tau> (NODE parent children) \<and> p |\<in>| \<delta>\<^sub>\<tau> witness" using b109 by auto
    have k98 : " nodesTail = [] \<Longrightarrow> \<exists>witness. witness \<in> \<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) (hd run) \<and> \<delta>\<^sub>\<tau> witness |\<subseteq>| \<delta>\<^sub>\<tau> (NODE parent children) \<and> p |\<in>| \<delta>\<^sub>\<tau> witness"
    proof -
      assume k100 : " nodesTail = []"
      from b117 b109 have "mirror \<in> (Z \<N> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) (hd run)))" by auto
      then have q1 : "mirror \<in> \<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) (hd run)" using Z_def by blast
      from b116  a2 b100 v100 have q2 : "\<delta>\<^sub>\<tau> mirror |\<subseteq>| \<delta>\<^sub>\<tau> (NODE parent children)"  by metis
      from b106 have b106b : "nodeListFitsPath pTail nodesTail" by auto
      then have b150 : "pTail = []" using k100  nodeListFitsPath.elims(2) by blast 
      have q3 : "p |\<in>| \<delta>\<^sub>\<tau> mirror"
      proof -
        from b101 b150 have b152 : "p = [pHead]" by auto
        from a4 nodeListFitsPath.simps(2) b100 b101 have b160 : "pHead = (root (down nodesRoot))" by auto
        then have b161 : "pHead = (root (down (hd nodeList)))" using b100 by auto
        from a2 b161 root.simps have b151 : "pHead = parent" by auto 
        from q1 root.simps have b154 : " (root mirror = symbol  (hd run))"
          using \<open>labelOfNode nodesRoot = root mirror\<close> b109 b130 by auto   
        have u7687 :  "symbol  (hd run) = parent"
          using \<open>labelOfNode nodesRoot = root mirror\<close> b111 b130 b151 b154 b160 by auto         
        from b154 b151 b152 u7687 have b153 : "[parent] |\<in>| \<delta>\<^sub>\<tau> mirror" using \<Pi>.simps root.elims
        proof -
          from b154 b151 b152 u7687 have "parent = root mirror" by auto
          then show "[parent] |\<in>| \<delta>\<^sub>\<tau> mirror" using rootIsPath root.simps                by (metis childrenSet.cases)  
        qed
        from b151 b153 b152 show  "p |\<in>| \<delta>\<^sub>\<tau> mirror" by auto
      qed
      from q1 q2 q3 show "\<exists>witness. witness \<in> \<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) (hd run) \<and> \<delta>\<^sub>\<tau> witness |\<subseteq>| \<delta>\<^sub>\<tau> (NODE parent children) \<and> p |\<in>| \<delta>\<^sub>\<tau> witness" by auto 
    qed
    have k97 : " nodesTail = [] \<or>  nodesTail \<noteq> []" by auto
    from k99 k98 k97 show "\<exists>witness. witness \<in> \<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>) (hd run) \<and> \<delta>\<^sub>\<tau> witness |\<subseteq>| \<delta>\<^sub>\<tau> (NODE parent children) \<and> p |\<in>| \<delta>\<^sub>\<tau> witness" by auto
  qed
qed
  
  
lemma pathsForestTree:
  fixes t
  shows "\<Union>| (\<Pi> |`| (finsert t {||})) =  \<Pi> t"
  using fimageE ffUnion_upper by auto
    
    
lemma treeInForestLang :
  assumes "f \<in> \<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>)  rule"
  defines "forest == (finsert f {||})"
  shows "forest \<in> \<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>) rule"
proof -
  have "tree_for_rule (\<A> \<ii>) rule f" using assms language_for_rule_def by auto
  have a1 : "(\<forall>tree.(tree|\<in>|forest \<longrightarrow>  tree_for_rule (\<A> \<ii>) rule tree))" by (simp add: \<open>tree_for_rule (\<A> \<ii>) rule f\<close> forest_def)
  from forest_language_for_rule_def a1 show "forest \<in> \<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>) rule"
    by (simp add: forest_language_for_rule_def finsertI1 forest_def) 
qed
  
lemma inUplus :
  fixes l L f
  assumes "l |\<in>| L"
  assumes "f \<in> l"
  shows "f \<in> \<Uplus> L"
  using assms(1) assms(2) biguplusForests_def by blast
    
    
lemma inUplusRules :
  assumes "r |\<in>| \<R> \<ii>"
  assumes "f \<in> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>) r)"
  shows "f \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>) |`| (\<R> \<ii>))"
  using inUplus assms by auto
    
    
lemma existsWitnessTree :
  fixes \<ii> f
  assumes "height f \<le> \<N>"
  shows "\<And> \<R> .  \<And> p . (  p |\<in>| \<Pi> f \<Longrightarrow>
                        f |\<in>| (\<Z>\<^sub>\<tau> n (\<P>\<^sub>1 \<R> \<ii>)) \<Longrightarrow>
                         (\<exists> witness .(witness \<in> (((\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>)) |`| (\<R> \<ii>)))))) \<and>  pathsInForest witness  |\<subseteq>| \<Pi> f \<and> p |\<in>| pathsInForest witness)))"
proof -
  fix p \<R>
  assume "p |\<in>| \<Pi> f"
  def nodes == "(nodeListForPath p f)"
  have "nodeListFitsPath p nodes" by (simp add: \<open>p |\<in>| \<delta>\<^sub>\<tau> f\<close> nodeListForPathExists nodes_def)
  have "nodes \<in> (pathsInTree f)"
    by (simp add: \<open>p |\<in>| \<delta>\<^sub>\<tau> f\<close> nodeListFitsTree nodes_def)
  assume "f |\<in>| (\<Z>\<^sub>\<tau> n (\<P>\<^sub>1 \<R> \<ii>))"
  have "pathSatisfiesApproximatorForRuleSet nodes (\<R> \<ii>) \<ii>" by (metis \<P>\<^sub>1_def \<open>f |\<in>| \<Z>\<^sub>\<tau> n (\<P>\<^sub>1 \<R> \<ii>)\<close> \<open>nodes \<in> pathsInTree f\<close> mem_Collect_eq satisfiesApproximatorForRuleSet_def zIntersectLemma)
  obtain run where o3 : "(hd run |\<in>| (\<R> \<ii>)) \<and>
                      (pathFitsListAndListIsARun \<ii> nodes run)" using \<open>pathSatisfiesApproximatorForRuleSet nodes (\<R> \<ii>) \<ii>\<close> pathSatisfiesApproximatorForRuleSet_def by auto
  have h657 : "isAPathp nodes" using \<open>nodes \<in> pathsInTree f\<close> pathsInTree_def by auto
  have "down (hd nodes) = f" by (metis (no_types, lifting) \<open>nodes \<in> pathsInTree f\<close> hasRoot list.sel(1) noEmptyPathsInTree nodeListForPath.elims nodes_def)
  from h657 isAPath.simps have "nodes \<noteq> []"    using isAPath_def by blast 
  then have o1 : " \<exists> witness . 
 (witness \<in> ((((((\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>))  (hd run))))))
  \<and> \<delta>\<^sub>\<tau> witness |\<subseteq>| \<delta>\<^sub>\<tau> f
  \<and> p |\<in>| \<delta>\<^sub>\<tau> witness)" using \<open>down (hd nodes) = f\<close> \<open>hd run |\<in>| \<R> \<ii> \<and> pathFitsListAndListIsARun \<ii> nodes run\<close> \<open>isAPathp nodes\<close> \<open>nodeListFitsPath p nodes\<close> existsWitnessTree2 assms by auto 
  show "\<exists>witness. witness \<in>  \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>) |`| \<R> \<ii>) \<and> \<Pi>\<^sub>\<iota>\<^sub>\<phi> witness |\<subseteq>| \<delta>\<^sub>\<tau> f \<and> p |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> witness"
  proof -
    from o1 obtain witness where o2 : "(witness \<in> ((((((\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> \<ii>))  (hd run)))))) \<and> \<delta>\<^sub>\<tau> witness |\<subseteq>| \<delta>\<^sub>\<tau> f  \<and> p |\<in>| \<delta>\<^sub>\<tau> witness)" by auto
    define witnessForest where "witnessForest == (finsert witness {||})"
    from o2 o3 treeInForestLang have "witnessForest \<in> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>) (hd run))" using witnessForest_def by auto 
    then have "witnessForest \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>) |`| \<R> \<ii>)" using o3 inUplusRules by auto
    have "\<Pi>\<^sub>\<iota>\<^sub>\<phi> witnessForest =  \<delta>\<^sub>\<tau> witness"
    proof -
      have "\<Pi>\<^sub>\<iota>\<^sub>\<phi> witnessForest = \<Union>| (\<Pi> |`| (finsert witness {||}))"
        by (simp add: pathsInForest_def witnessForest_def) 
      then show "\<Pi>\<^sub>\<iota>\<^sub>\<phi> witnessForest =  \<delta>\<^sub>\<tau> witness" using pathsForestTree by auto 
    qed
    from o2 witnessForest_def have "\<Pi>\<^sub>\<iota>\<^sub>\<phi> witnessForest |\<subseteq>| \<delta>\<^sub>\<tau> f" using \<open>\<Pi>\<^sub>\<iota>\<^sub>\<phi> witnessForest = \<delta>\<^sub>\<tau> witness\<close> by auto
    from o2 witnessForest_def have "p |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> witnessForest" using \<open>\<Pi>\<^sub>\<iota>\<^sub>\<phi> witnessForest = \<delta>\<^sub>\<tau> witness\<close> by auto
    show "\<exists>witness. witness \<in>  \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>) |`| \<R> \<ii>) \<and> \<Pi>\<^sub>\<iota>\<^sub>\<phi> witness |\<subseteq>| \<delta>\<^sub>\<tau> f \<and> p |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> witness" using \<open>\<Pi>\<^sub>\<iota>\<^sub>\<phi> witnessForest |\<subseteq>| \<delta>\<^sub>\<tau> f\<close> \<open>p |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> witnessForest\<close> \<open>witnessForest \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>) |`| \<R> \<ii>)\<close> by auto
  qed
qed
  
lemma smallerThanN :
  fixes \<ii> f
  assumes "n \<le> \<N>"
  shows "\<And> \<R> .   (  
                        f |\<in>| (\<Z>\<^sub>\<tau> n (\<P>\<^sub>1 \<R> \<ii>)) \<Longrightarrow>
                        \<Pi> f \<in> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (((\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>)) |`| (\<R> \<ii>)))))))"
proof -
  fix \<R>
  assume a2 : "f |\<in>| (\<Z>\<^sub>\<tau> n (\<P>\<^sub>1 \<R> \<ii>))"
  have "height f \<le> \<N>" by (smt Z_def \<Z>\<tau>_lemma \<open>f |\<in>| \<Z>\<^sub>\<tau> n (\<P>\<^sub>1 \<R> \<ii>)\<close> assms dual_order.trans fmember.rep_eq mem_Collect_eq)
  then have a1: "\<And> p . (  p |\<in>| \<Pi> f \<Longrightarrow>
                        f |\<in>| (\<Z>\<^sub>\<tau> n (\<P>\<^sub>1 \<R> \<ii>)) \<Longrightarrow>
                         (\<exists> witness .(witness \<in> (((\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>)) |`| (\<R> \<ii>)))))) \<and>  pathsInForest witness  |\<subseteq>| \<Pi> f \<and> p |\<in>| pathsInForest witness)))" using existsWitnessTree by auto
  def collectWitnesses == "\<lambda> p .  (SOME witness .(witness \<in> (((\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>)) |`| (\<R> \<ii>)))))) \<and>  pathsInForest witness  |\<subseteq>| \<Pi> f \<and> p |\<in>| pathsInForest witness))"
  from a1 collectWitnesses_def a2 someI have 
    a3 : "\<And> p . (  p |\<in>| \<Pi> f \<Longrightarrow> ((collectWitnesses p) \<in> (((\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>)) |`| (\<R> \<ii>)))))) \<and>  pathsInForest (collectWitnesses p)  |\<subseteq>| \<Pi> f \<and> p |\<in>| pathsInForest (collectWitnesses p)))" by (metis (mono_tags, lifting))   
  def witnessForest == "\<Union>| (collectWitnesses |`| (\<Pi> f))"
  have "\<Pi> f = \<Pi>\<^sub>\<iota>\<^sub>\<phi> witnessForest"
  proof 
    show "\<delta>\<^sub>\<tau> f |\<subseteq>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> witnessForest"
    proof 
      fix p
      assume "p|\<in>| \<delta>\<^sub>\<tau> f"
      then have " p |\<in>| pathsInForest (collectWitnesses p)" using a3 by auto
      then have "p |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Union>| (collectWitnesses |`| (\<Pi> f)))" by (smt \<open>p |\<in>| \<delta>\<^sub>\<tau> f\<close> ffUnionI ffUnionLemma ffUnion_Pow_eq ffsubset_Pow_Union fimageE fimage_finsert finsert_fsubset mk_disjoint_finsert pathsInForest_def)
      then show "p |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> witnessForest" using witnessForest_def by auto
    qed
    show " \<Pi>\<^sub>\<iota>\<^sub>\<phi> witnessForest |\<subseteq>| \<delta>\<^sub>\<tau> f"
    proof -
      from witnessForest_def have  "\<Pi>\<^sub>\<iota>\<^sub>\<phi> witnessForest = \<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Union>| (collectWitnesses |`| (\<Pi> f)))" by auto
      from a3 have "\<And> f2 . f2 |\<in>| ((collectWitnesses |`| (\<Pi> f))) \<Longrightarrow> \<Pi>\<^sub>\<iota>\<^sub>\<phi> f2 |\<subseteq>| \<delta>\<^sub>\<tau> f" using fimageE by auto
      have a4 : "\<Pi>\<^sub>\<iota>\<^sub>\<phi> witnessForest = \<Union>| (\<Pi> |`| witnessForest)" by (simp add: pathsInForest_def) 
      from witnessForest_def have "\<And> f2 . f2 |\<in>| witnessForest \<Longrightarrow> (\<exists> p2 . p2 |\<in>| (\<Pi> f) \<and> f2 |\<in>| (collectWitnesses p2))" using ffUnionLemma fimageE by auto
          
      then have "\<And> f2 . f2 |\<in>| witnessForest \<Longrightarrow> (\<exists> p2 . p2 |\<in>| (\<Pi> f) \<and> \<Pi> f2 |\<subseteq>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> (collectWitnesses p2))" using pathsInForest_def by fastforce
      then have "\<And> f2 . f2 |\<in>| witnessForest \<Longrightarrow> (\<Pi> f2 |\<subseteq>| \<Pi> f)" using a3 by fastforce
      then show " \<Pi>\<^sub>\<iota>\<^sub>\<phi> witnessForest |\<subseteq>| \<delta>\<^sub>\<tau> f" using a4 pathsInForest_def using fPowI ffUnion_Pow_eq ffUnion_mono fimage_fsubsetI by fastforce
    qed
  qed
  have "witnessForest \<in> (((\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>)) |`| (\<R> \<ii>))))))"
  proof -
    from a3 have  "\<And> p . (  p |\<in>| \<Pi> f \<Longrightarrow> ((collectWitnesses p) \<in> (((\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>)) |`| (\<R> \<ii>))))))))" by auto
    then show "witnessForest \<in> (((\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>)) |`| (\<R> \<ii>))))))" using biguplusForests_def      by (smt ffUnionI ffUnionLemma fimageE fset_rev_mp fsubsetI mem_Collect_eq witnessForest_def) 
  qed
  show "\<delta>\<^sub>\<tau> f \<in> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>) |`| \<R> \<ii>)" using \<open>\<delta>\<^sub>\<tau> f = \<Pi>\<^sub>\<iota>\<^sub>\<phi> witnessForest\<close> \<open>witnessForest \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>) |`| \<R> \<ii>)\<close> by auto 
qed
  
  (* ============================================== *)
  
  
lemma differentPZLemma:
  shows "UNION (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2) fset =  \<Pi>\<^sub>\<phi> ((\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2))"
proof -
  from \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta>_def have "UNION (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2) fset = UNION (\<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> \<circ> \<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1) |`| Sa1) \<inter> \<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> \<circ> \<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2) |`| Sa2)) fset" by auto
  from \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>_def have a1 : "\<Pi>\<^sub>\<phi> (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2) = \<Pi>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1 |`| Sa1) \<inter> \<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2 |`| Sa2))" by auto
  have "\<And> k .\<Pi>\<^sub>\<phi> (k) = UNION (\<Pi>\<^sub>\<iota>\<^sub>\<phi> `(k)) fset" using pathsArbitraryUnionLemma    by auto  
  hence "\<And> k l .\<Pi>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> ` k \<inter> \<Psi>\<^sub>\<phi> ` l) = UNION (\<Pi>\<^sub>\<iota>\<^sub>\<phi> `(\<Psi>\<^sub>\<phi> ` k \<inter> \<Psi>\<^sub>\<phi> ` l)) fset" by auto
  then have "\<Pi>\<^sub>\<phi> (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2) = UNION (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1 |`| Sa1) \<inter> \<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2 |`| Sa2))) fset" using a1 by auto
  have "(\<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> \<circ> \<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1) |`| Sa1) \<inter> \<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> \<circ> \<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2) |`| Sa2)) = (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1 |`| Sa1) \<inter> \<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2 |`| Sa2)))" using \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta>_def \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>_def psiDeltaPsi by presburger 
  show ?thesis    using \<open>UNION (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2) fset = UNION (\<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> \<circ> \<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1) |`| Sa1) \<inter> \<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> \<circ> \<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2) |`| Sa2)) fset\<close> \<open>\<Pi>\<^sub>\<phi> (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2) = UNION (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1 |`| Sa1) \<inter> \<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2 |`| Sa2))) fset\<close> \<open>\<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> \<circ> \<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1) |`| Sa1) \<inter> \<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> \<circ> \<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2) |`| Sa2) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1 |`| Sa1) \<inter> \<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2 |`| Sa2))\<close> by presburger 
qed
  
  
lemma nodeListForPath_lemma :
  fixes p f
  assumes "p |\<in>| \<delta>\<^sub>\<tau> f"
  defines "nodeList \<equiv> nodeListForPath p f"
  shows "nodeList \<in> (pathsInTree f)"
  by (simp add: assms(1) nodeListFitsTree nodeList_def)
    
    
    
    (* =================================================== *)
    
    (* Here, the goal is to show the difficult direction for depth > N (the Main Lemma from the writeup) *)
    
    
lemma emptyPathNotInI :
  assumes "    I \<in> \<I>"
  shows "[] \<notin> I"
proof -
  from assms obtain language1 language2 where "I = ((\<Pi>\<^sub>\<phi> language1)) -(\<Pi>\<^sub>\<delta>  language2)" using \<I>_def
    by (smt image_iff mem_Collect_eq) 
  from pathsForForestLanguage_def pathsInForest_def \<Pi>.simps have "[] \<notin> \<Pi>\<^sub>\<phi> language1"
  proof -
    obtain tt :: "abc tree fset \<Rightarrow> abc list \<Rightarrow> abc tree" where
      "\<forall>as f. (as |\<notin>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> f \<or> tt f as |\<in>| f \<and> as |\<in>| \<delta>\<^sub>\<tau> (tt f as)) \<and> (as |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> f \<or> (\<forall>t. t |\<notin>| f \<or> as |\<notin>| \<delta>\<^sub>\<tau> t))"
      by (metis pathsTreeForest)
    then have "\<nexists>f. f \<in> language1 \<and> [] |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> f"
      by (meson list.distinct(1) noEmptyPathsInPi)
    then show ?thesis
      using pathsForForestLanguage_def by auto
  qed
  then show ?thesis        using \<open>I = \<Pi>\<^sub>\<phi> language1 - UNION language2 fset\<close> by auto 
qed
  
  
  
lemma finiteMonotoneStationary :
  fixes w
  assumes "\<And> n . w (Suc n) |\<subseteq>| w n"
  shows "\<exists>n.(\<forall>k0. (n \<le> k0 \<longrightarrow> w k0 = w (Suc k0)))"
proof 
  def disappearing == "\<lambda> z. (\<exists> n0. z |\<notin>| w n0)"
  def disappearingElements == "ffilter disappearing (w 0)"
  def disappearsAt == "\<lambda> z.(SOME n0. z |\<notin>| w n0)"
    
  have n655876 :  "\<And> n1 n2 . n1 \<ge> n2 \<Longrightarrow> w n1 |\<subseteq>| w n2"
  proof -
    fix n1 n2
    show  "n1 \<ge> n2 \<Longrightarrow> w n1 |\<subseteq>| w n2"
    proof (induct "n1")
      case 0
      then have "n2 = 0" by arith
      then have "w 0 = w n2" by auto
      then have "w 0 |\<subseteq>| w n2" by auto
      then show ?case by auto
    next
      case (Suc n1)
      assume n6y76897 : "n2 \<le> Suc n1"
      show ?case 
      proof (rule disjE)
        from n6y76897 show "n1  \<ge> n2 \<or> Suc n1 = n2"  by arith
        show "n1  \<ge> n2 \<Longrightarrow> w (Suc n1) |\<subseteq>| w n2 " using assms Suc.hyps by auto
        show "Suc n1 = n2 \<Longrightarrow> w (Suc n1) |\<subseteq>| w n2 "  by auto
      qed
    qed
  qed
    
  have n675687 : "\<And>z . disappearing z \<Longrightarrow> (\<And> n . n \<ge> (disappearsAt z) \<Longrightarrow> z |\<notin>| (w n))"
  proof -
    fix z
    assume "disappearing z"
    then obtain n0 where "z |\<notin>| w n0" using disappearing_def by auto
    hence n5r87 :  "z |\<notin>| w (disappearsAt z)" using disappearsAt_def someI_ex by metis
    fix n
    show "n \<ge> (disappearsAt z) \<Longrightarrow> z |\<notin>| (w n)"
    proof (induct "n" arbitrary: ks rule: less_induct)
      case (less x)
      then show ?case using n5r87 n655876 by blast 
    qed
  qed
    
  def n == "maxFset (disappearsAt |`| (ffilter disappearing (w 0)))"
  show "(\<forall>k0. (n \<le> k0 \<longrightarrow> w k0 = w (Suc k0)))"
  proof
    fix k0
    show " n \<le> k0 \<longrightarrow> w k0 = w (Suc k0)"
    proof
      assume n7575 : " n \<le> k0"
      show " w k0 = w (Suc k0)"
      proof (rule ccontr)
        assume "w k0 \<noteq> w (Suc k0)"
        then obtain differing where n54877 : "differing |\<in>| w k0" and n76686 : "differing |\<notin>| w (Suc k0)" using assms
          by blast 
        then have "differing |\<in>| w 0" using n655876
          by blast 
        then have ny7656876 :  "differing |\<in>| (ffilter disappearing (w 0))" using n76686 disappearing_def by auto
        then have "differing |\<notin>| w (disappearsAt differing)" using n675687 by simp
        then have "differing |\<notin>| w n" using n_def ny7656876
          by (simp add: finiteMaxExists(1) n675687) 
        then have "differing |\<notin>| w k0 " using n7575 n655876 by auto
        then show "False" using n54877 by auto
      qed
    qed
  qed
qed
  
  
    
    
lemma core_main_lemma :
  fixes l
  fixes \<R>
  fixes n
  fixes j          
  fixes \<alpha>
    assumes allRulesArePresent : "(\<And>i rule. rule |\<in>| rule_set (\<A> i))"
  assumes   rulesLangsNonempty : "\<And> \<R> i r . (r |\<in>| rule_set (\<A> i) \<Longrightarrow>  ((\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) r)  \<noteq> {}))"
  assumes "\<And> r i. r |\<in>| \<R> i \<Longrightarrow> (r |\<in>| rule_set (\<A> i) \<and> symbol r = \<alpha>)"
  assumes statesLanguagesNonempty : "\<And> \<ii> r. r |\<in>| (\<R> \<ii>) \<Longrightarrow>   (\<And> s . s |\<in>| (states r) \<Longrightarrow> ((\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>) s)  \<noteq> {}))"
  assumes alphaIsTransition : "\<And> \<ii> rule . rule |\<in>| (\<R> \<ii>) \<Longrightarrow> symbol rule = \<alpha>"
  assumes fNotEmpty : "fset (\<ff> (Suc n)  \<R>) \<noteq> {}"
  assumes outerHypothesis : "\<And> rs2. (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> n  rs2))) = \<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> n rs2))"
  assumes inStateSet : "\<And> \<ii>. \<And> r . \<And> s . r |\<in>| (\<R> \<ii>) \<Longrightarrow> s |\<in>| states r \<Longrightarrow> s |\<in>| state_set (\<A> \<ii>)"
  assumes nAssum : "Suc n > \<N>"
  shows "(\<exists> k. (\<ff>\<^sub>1 n k \<R>) = {||}) \<or> (\<exists>k . ( \<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)) \<union> {[]}) =  \<Pi>\<^sub>\<tau>\<^sub>F ((  \<gg> (Suc n) \<R>))))"
and "\<And> k . (\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) |\<subseteq>| \<ff>\<^sub>1 n k \<R>"
proof -
(*  show "(\<exists> k. (\<ff>\<^sub>1 n k \<R>) = {||}) \<or> (\<not>(\<exists> k. (\<ff>\<^sub>1 n k \<R>) = {||}))" by auto*)

(*  show "(\<exists> k. (\<ff>\<^sub>1 n k \<R>) = {||}) \<Longrightarrow> ((\<exists> k. (\<ff>\<^sub>1 n k \<R>) = {||}) \<or> (\<exists>k . ( \<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)) \<union> {[]}) =  \<Pi>\<^sub>\<tau>\<^sub>F ((  \<gg> (Suc n) \<R>)) \<and> (\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) |\<subseteq>| \<ff>\<^sub>1 n k \<R>)))" by auto*)
      

      
  
  have wSymbol : "\<And> k \<ii> rule . rule |\<in>| ((\<W> n k \<R>) \<ii>) \<Longrightarrow> symbol rule = \<alpha>" using alphaIsTransition
    by (meson fset_rev_mp wInR)
      
  have firstGoal : "\<And>k. (\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) |\<subseteq>| \<ff>\<^sub>1 n k \<R>" (* (a) *)
    and secondGoal : "\<And>k.(\<ff>\<^sub>1 n (Suc k) \<R>) = \<Z>\<^sub>\<tau> n (\<P>\<^sub>\<sigma> (\<W> n k \<R>))" (* (b) *)
    and fourthGoal : "\<And>k.(\<exists> e . k = Suc e) \<Longrightarrow> (thereIsAnUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))) \<Longrightarrow>
          \<exists>I\<in>\<I>.  (\<V>\<^sub>\<tau> (\<pi>\<^sup>1 (chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))))   (\<pi>\<^sup>2 (  chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))    ))) \<Turnstile> (\<alpha> \<bullet> I) 
                  \<and> I \<inter> \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)) = {}" (* (d) *)
    and seventhGoal : "\<And>k.(\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n (Suc k) \<R>)) = \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>1))   (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>2)))))"
  proof -
    fix k
    show secondGoal : "\<And>k . (\<ff>\<^sub>1 n (Suc k) \<R>) = \<Z>\<^sub>\<tau> n (\<P>\<^sub>\<sigma> (\<W> n k \<R>))"
    proof -
      fix k
      show  "(\<ff>\<^sub>1 n (Suc k) \<R>) = \<Z>\<^sub>\<tau> n (\<P>\<^sub>\<sigma> (\<W> n k \<R>))"
      proof (induct "k" arbitrary: ks rule: less_induct)
        fix k
        assume hyp2a1 : "(\<And> y. y < k \<Longrightarrow>  \<ff>\<^sub>1 n (Suc y) \<R> = \<Z>\<^sub>\<tau> n (\<P>\<^sub>\<sigma> (\<W> n y \<R>)))"
        have b64 : "(\<ff>\<^sub>1 n (Suc k) \<R>) = inf_fset2 (\<ff>\<^sub>1 n k \<R>)  (\<P>\<^sub>\<sigma> (\<W> n (k) \<R>))" by auto
            
        show "(\<ff>\<^sub>1 n (Suc k) \<R>) = \<Z>\<^sub>\<tau> n (\<P>\<^sub>\<sigma> (\<W> n k \<R>))"
        proof (rule disjE)
          show "k = 0 \<or> k > 0" by auto
          {
            assume "k > 0"
            then obtain e where b65 : "k = Suc e"          using gr0_implies_Suc by blast 
            from hyp2a1 b65 have b67 : "(\<ff>\<^sub>1 n k \<R>) = \<Z>\<^sub>\<tau> n (\<P>\<^sub>\<sigma> (\<W> n e \<R>))" by blast
            have b66 : "\<Z>\<^sub>\<tau> n (\<P>\<^sub>\<sigma> (\<W> n k \<R>)) |\<subseteq>| \<Z>\<^sub>\<tau> n (\<P>\<^sub>\<sigma> (\<W> n e \<R>))" by (metis \<P>\<sigma>_mono \<ff>\<^sub>1.simps(1) b65 fbBoundedDepth finter_mono wMonotonic zIntersectLemmaFin) 
            have b68 : "(\<ff>\<^sub>1 n (Suc k) \<R>) = (\<ff>\<^sub>1 n k \<R>) |\<inter>| (\<Z>\<^sub>\<tau> n  (\<P>\<^sub>\<sigma> (\<W> n (k) \<R>)))"
            proof -
              have q91 : "(\<ff>\<^sub>1 n k \<R>) |\<subseteq>| \<Z>\<^sub>\<tau> n UNIV" by (simp add: fbBoundedDepth) 
              from zIntersectLemmaFin have q92 : "(\<Z>\<^sub>\<tau> n  (\<P>\<^sub>\<sigma> (\<W> n (k) \<R>))) = inf_fset2 (\<Z>\<^sub>\<tau> n UNIV) (\<P>\<^sub>\<sigma> (\<W> n (k) \<R>))" by metis 
              from q91 q92 show "(\<ff>\<^sub>1 n (Suc k) \<R>) = (\<ff>\<^sub>1 n k \<R>) |\<inter>| (\<Z>\<^sub>\<tau> n  (\<P>\<^sub>\<sigma> (\<W> n (k) \<R>)))" by (metis b64 finter_assoc inf_absorb1) 
            qed
            have b69 : "(\<Z>\<^sub>\<tau> n  (\<P>\<^sub>\<sigma> (\<W> n (k) \<R>))) |\<subseteq>| (\<ff>\<^sub>1 n k \<R>) " by (simp add: b66 b67) 
            show "(\<ff>\<^sub>1 n (Suc k) \<R>) = \<Z>\<^sub>\<tau> n (\<P>\<^sub>\<sigma> (\<W> n k \<R>))" using b66 b67 b68 inf.absorb_iff2 by auto 
          }
          {
            assume b62 : "k=0"
            have b63 : "\<ff>\<^sub>1 n (Suc 0) \<R> = inf_fset2 (\<ff>\<^sub>1 n 0 \<R>)  (\<P>\<^sub>\<sigma> (\<W> n (0) \<R>))" by simp
            have b64 : "(\<ff>\<^sub>1 n 0 \<R>) = \<Z>\<^sub>\<tau> n UNIV" by simp
            from b63 b64          have "\<ff>\<^sub>1 n (Suc 0) \<R> =  (\<Z>\<^sub>\<tau> n (\<P>\<^sub>\<sigma> (\<W> n (0) \<R>)))"            by (metis zIntersectLemmaFin) 
            then show "(\<ff>\<^sub>1 n (Suc k) \<R>) = \<Z>\<^sub>\<tau> n (\<P>\<^sub>\<sigma> (\<W> n k \<R>))" using b62 by auto
          }
        qed
      qed
    qed
      
      
      (* Here, the outer induction hypothesis is used *)
    show seventhGoal : "\<And>k.(\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n (Suc k) \<R>)) = \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>1))   (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>2)))))"
    proof -
      fix k
      show "(\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n (Suc k) \<R>)) = \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>1))   (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>2)))))"
      proof -
        from secondGoal have "\<And> k0. k0 \<le> Suc k \<Longrightarrow> (\<ff>\<^sub>1 n (Suc k) \<R>) = \<Z>\<^sub>\<tau> n (\<P>\<^sub>\<sigma> (\<W> n k \<R>))" by auto
        def downRules == "\<lambda> \<ii> . (\<Union>| (rulesForState \<ii> |`| (stateSetFromRuleSet (\<W> n k \<R> \<ii>))))"
          
        have m330 : "\<P>\<^sub>\<sigma> (\<W> n k \<R>) = (\<P> downRules)"
        proof -
          from satisfiesApproximatorForStatesFromRuleSet_def \<P>\<^sub>\<sigma>_def have m340 : 
            "\<And> tr . tr \<in> \<P>\<^sub>\<sigma> (\<W> n k \<R>) = (\<forall>\<ii>.((\<forall> p \<in> (pathsInTree tr) . 
             pathSatisfiesApproximatorForStateFromRuleSet p (\<W> n k \<R> \<ii>) \<ii>)))" by blast
          from satisfiesApproximatorForRuleSet_def  \<P>_def have m341 :
            "\<And> tr . tr \<in> \<P> downRules = (\<forall>\<ii>.((\<forall> p \<in> (pathsInTree tr) . 
             pathSatisfiesApproximatorForRuleSet  p (downRules \<ii>) \<ii>)))" by blast
          from pathSatisfiesApproximatorForRuleSet_def have m349 : "\<And> \<ii> p tr. (pathSatisfiesApproximatorForRuleSet  p (downRules \<ii>) \<ii> =  (\<exists> r  . (hd r |\<in>| (downRules \<ii>)) \<and>
                      (pathFitsListAndListIsARun \<ii> p r)))" by blast
          from pathSatisfiesApproximatorForStateFromRuleSet_def have m350 : "\<And> \<ii> tr p.(pathSatisfiesApproximatorForStateFromRuleSet p (\<W> n k \<R> \<ii>) \<ii> = 
                (\<exists> r  . \<exists>rule. rule |\<in>| ((\<W> n k \<R> \<ii>)) \<and> ((stateFromRule  \<ii> (hd r)) |\<in>| (states rule)) \<and>
                      (pathFitsListAndListIsARun \<ii> p r)))" by (metis notin_fset) 
          have m351 : "\<And> \<ii> p tr r. ((pathFitsListAndListIsARun \<ii> p r) \<Longrightarrow> (p = [] \<or> ((hd r |\<in>| (downRules \<ii>))) = ( \<exists>rule. rule |\<in>| (\<W> n k \<R> \<ii>) \<and> ((stateFromRule  \<ii> (hd r)) |\<in>| (states rule))     )))"
          proof -
            fix \<ii> p tr r
            assume g372 : "(pathFitsListAndListIsARun \<ii> p r)"
            from downRules_def ffUnionLemma have u10 : "(((hd r |\<in>| (downRules \<ii>))) = (\<exists>state .(state |\<in>|  (stateSetFromRuleSet (\<W> n k \<R> \<ii>)) \<and> (hd r) |\<in>| (rulesForState \<ii> state))))" using ffUnionI fimageE fimage_eqI by auto
            have u11 : "\<And> state . ( (state |\<in>|  (stateSetFromRuleSet (\<W> n k \<R> \<ii>))  = (\<exists>rule.(rule |\<in>| (\<W> n k \<R> \<ii>) \<and> state |\<in>| states rule))))"
            proof
              from stateSetFromRuleSet_def fimageE  ffUnionLemma  
              show "\<And>state. state |\<in>| stateSetFromRuleSet (\<W> n k \<R> \<ii>) \<Longrightarrow> \<exists>rule. rule |\<in>| \<W> n k \<R> \<ii> \<and> state |\<in>| states rule" by metis
              from stateSetFromRuleSet_def ffUnionI  fimage_eqI    
              show "\<And>state. \<exists>rule. rule |\<in>| \<W> n k \<R> \<ii> \<and> state |\<in>| states rule \<Longrightarrow> state |\<in>| stateSetFromRuleSet (\<W> n k \<R> \<ii>)" by metis
            qed
            from rulesForState_def 
            have u12: "\<And> state. ((hd r) |\<in>| (rulesForState \<ii> state) = ((hd r) |\<in>| (rule_set (\<A> \<ii>)) \<and> transition (\<A> \<ii>) (states (hd r)) (symbol (hd r)) = state))" by (simp add: ffmember_filter)
            from u11 have u21 : "(\<exists>state .(state |\<in>|  (stateSetFromRuleSet (\<W> n k \<R> \<ii>)) \<and> (hd r) |\<in>| (rulesForState \<ii> state))) 
           =  (\<exists>state .((\<exists>rule.(rule |\<in>| (\<W> n k \<R> \<ii>) \<and> state |\<in>| states rule)) \<and> (hd r) |\<in>| (rulesForState \<ii> state)))  " by auto
            from u12 u21 have u22 : "(\<exists>state .(state |\<in>|  (stateSetFromRuleSet (\<W> n k \<R> \<ii>)) \<and> (hd r) |\<in>| (rulesForState \<ii> state))) 
          =  (\<exists>state .((\<exists>rule.(rule |\<in>| (\<W> n k \<R> \<ii>) \<and> state |\<in>| states rule)) \<and> ((hd r) |\<in>| (rule_set (\<A> \<ii>)) \<and> transition (\<A> \<ii>) (states (hd r)) (symbol (hd r)) = state)))" by auto
            from u22 u10 have u23 : "(hd r |\<in>| (downRules \<ii>))
          =  (\<exists>state .((\<exists>rule.(rule |\<in>| (\<W> n k \<R> \<ii>) \<and> state |\<in>| states rule)) \<and> ((hd r) |\<in>| (rule_set (\<A> \<ii>)) \<and> transition (\<A> \<ii>) (states (hd r)) (symbol (hd r)) = state)))" by auto
            from u23 have u24 : "(hd r |\<in>| (downRules \<ii>))
          =  (((\<exists>rule.(rule |\<in>| (\<W> n k \<R> \<ii>) 
                       \<and> (transition (\<A> \<ii>) (states (hd r)) (symbol (hd r))) |\<in>| states rule)) 
                \<and> ((hd r) |\<in>| (rule_set (\<A> \<ii>)))))" by auto
            from g372 hd_Cons_tl pathFitsListAndListIsARun.simps(2) pathFitsListAndListIsARun.simps(3) have u25 : "((hd r) |\<in>| (rule_set (\<A> \<ii>))) \<or> p = []" by (metis)
            from u24 u25 have u1 : "p = [] \<or> (((hd r |\<in>| (downRules \<ii>))) = ( \<exists>rule . (rule |\<in>| (\<W> n k \<R> \<ii>) \<and> (transition (\<A> \<ii>) (states ((hd r))) (symbol ((hd r))))  |\<in>| (states rule)  )))" by metis 
            from stateFromRule_def have u2 : " ((stateFromRule  \<ii> (hd r))  = (transition (\<A> \<ii>) (states ((hd r))) (symbol ((hd r)))))" by metis
            from u1 u2 show "(p = [] \<or> (((hd r |\<in>| (downRules \<ii>))) =  ( \<exists>rule . rule |\<in>| (\<W> n k \<R> \<ii>) \<and> ((stateFromRule  \<ii> (hd r)) |\<in>| (states rule))     )))" by metis
          qed
          have m355 : "\<And> \<ii> p tr. (p = [] \<or> pathSatisfiesApproximatorForRuleSet  p (downRules \<ii>) \<ii> = pathSatisfiesApproximatorForStateFromRuleSet p (\<W> n k \<R> \<ii>) \<ii> )"
          proof -
            fix \<ii> p tr
            from m351  have m94268 : "\<And> r  . (p \<noteq> [] \<Longrightarrow> (((hd r |\<in>| (downRules \<ii>)) \<and> (pathFitsListAndListIsARun \<ii> p r))
                      = (\<exists>rule. rule |\<in>| ((\<W> n k \<R> \<ii>)) \<and> ((stateFromRule  \<ii> (hd r)) |\<in>| (states rule)) \<and>
                         (pathFitsListAndListIsARun \<ii> p r))))" by metis
            from m94268 show "(p = [] \<or> pathSatisfiesApproximatorForRuleSet  p (downRules \<ii>) \<ii> = pathSatisfiesApproximatorForStateFromRuleSet p (\<W> n k \<R> \<ii>) \<ii> )" using m349 m350 by metis 
          qed
          from m340 m341 m355 noEmptyPathsInTree have "\<And> tr . tr \<in> \<P>\<^sub>\<sigma> (\<W> n k \<R>) =  (tr \<in> \<P> downRules)" by metis
          then show "\<P>\<^sub>\<sigma> (\<W> n k \<R>) = (\<P> downRules)" by auto
        qed
        from m330 \<ff>_def have "\<ff> n downRules = \<Z>\<^sub>\<tau> n ( (\<P>\<^sub>\<sigma> (\<W> n k \<R>)))" by simp
        from m330 \<ff>_def outerHypothesis have "(\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> n ( (\<P>\<^sub>\<sigma> (\<W> n k \<R>))))) = \<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> n downRules))" by auto
        from \<gg>_def have "\<gg> n downRules = \<Union>| (\<Z>\<^sub>\<phi> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (((downRules) \<aa>\<^sub>1))((((downRules) \<aa>\<^sub>2)))))" by auto
        from \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>_def have d544 : "(\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>1))   (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>2))) 
                                = ( ((\<Psi>\<^sub>\<phi> `(\<Uplus> ( ((\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1) |`|  (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>1)))))) 
                                    \<inter> (\<Psi>\<^sub>\<phi> `(\<Uplus> ( ((\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2) |`|  (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>2))))))))" by auto
        from \<Psi>\<^sub>\<Sigma>\<^sub>\<rho>_def have d545 : "(\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (((downRules) \<aa>\<^sub>1))((((downRules) \<aa>\<^sub>2)))) =  
                                    (\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| (downRules \<aa>\<^sub>1))))) 
                                              \<inter> (\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>2) |`| (downRules \<aa>\<^sub>2)))))" by auto
        have j3653 : "\<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> n downRules)) = \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>1))   (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>2))))"
        proof -
          from psiRulesStatesLemma2 allRulesArePresent
          have "\<And>i . ((\<Psi>\<^sub>\<phi> `(\<Uplus> ( ((\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i)) |`|  (stateSetFromRuleSet (\<W> n k \<R> i))))))) = (\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i)) |`| ((\<Union>| (rulesForState i |`| (stateSetFromRuleSet (\<W> n k \<R> i))))))))) " 
            by auto
          then have "\<And>i . ((\<Psi>\<^sub>\<phi> `(\<Uplus> ( ((\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i)) |`|  (stateSetFromRuleSet (\<W> n k \<R> i))))))) = (\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i)) |`| (downRules i))))) " using downRules_def by auto
          then have "\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (((downRules) \<aa>\<^sub>1))((((downRules) \<aa>\<^sub>2))) = \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>1))   (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>2))" using aut_def d544 d545 by metis 
          then have f654 : "\<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (((downRules) \<aa>\<^sub>1))((((downRules) \<aa>\<^sub>2))))) =   \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>1))   (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>2))))" by auto
          from piUnionLemma have "\<And>l. \<Pi>\<^sub>\<tau>\<^sub>F ( \<Union>| (\<Z>\<^sub>\<phi> n l)) = \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n l)" by auto
          then show "\<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> n downRules)) = \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>1))   (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>2))))" using f654 \<gg>_def piUnionLemma by auto
        qed
        from piFset have f388525 : "\<And>l. \<Pi>\<^sub>\<tau>\<^sub>F l = (fset (\<Pi>\<^sub>\<iota>\<^sub>\<phi> l))" by auto
        have f472763 : "(fset (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ((\<Z>\<^sub>\<tau> n (\<P>\<^sub>\<sigma> (\<W> n k \<R>)))))) = \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>1))   (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>2))))"
        proof -   
          from outerHypothesis have j3652 : "\<And> rs2. (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> n  rs2))) = \<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> n rs2))" by auto (* this is a general fact for depth n, the previous iteration of the outer induction *)
          then have j3654 : "(\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> n  downRules))) = \<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> n downRules))" by auto
          then have j3655 : "(\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> n  downRules))) = \<Pi>\<^sub>\<tau>\<^sub>F (\<Union>| (\<Z>\<^sub>\<phi> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (((downRules) \<aa>\<^sub>1))((((downRules) \<aa>\<^sub>2))))))" using \<gg>_def by auto
          from j3653 have  "\<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> n downRules)) = \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>1))   (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>2))))" by auto
          from j3654 j3653 have j3657 : "(\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> n  downRules))) = \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>1))   (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>2))))" by auto
              
          from f388525 have j3658 : "(\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> n (\<P> downRules)) = (fset (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ((\<Z>\<^sub>\<tau> n (\<P> downRules))))))" by auto
          from \<ff>_def j3658 j3657 j3653 have "(fset (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ((\<Z>\<^sub>\<tau> n (\<P> downRules))))) = \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>1))   (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>2))))"  by auto
          then  show ?thesis using m330 by auto
        qed
        from secondGoal have "(\<ff>\<^sub>1 n (Suc k) \<R>) = \<Z>\<^sub>\<tau> n (\<P>\<^sub>\<sigma> (\<W> n k \<R>))" by auto
        then have "(fset (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ((\<Z>\<^sub>\<tau> n (\<P>\<^sub>\<sigma> (\<W> n k \<R>)))))) = (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n (Suc k) \<R>)))" using f388525 by auto
        then show "(\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n (Suc k) \<R>)) = \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>1))   (stateSetFromRuleSet (\<W> n k \<R> \<aa>\<^sub>2)))))" using f472763 by auto
      qed
    qed
      
      
    show fourth: "\<And>k.(\<exists> e . k = Suc e) \<Longrightarrow> (thereIsAnUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))) \<Longrightarrow>
          \<exists>I\<in>\<I>.  (\<V>\<^sub>\<tau> (\<pi>\<^sup>1 (chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))))   (\<pi>\<^sup>2 (  chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))    ))) \<Turnstile> (\<alpha> \<bullet> I) 
                  \<and> I \<inter> \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)) = {}"
    proof -
      fix k
      show "(\<exists> e . k = Suc e) \<Longrightarrow> (thereIsAnUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))) \<Longrightarrow>
          \<exists>I\<in>\<I>.  (\<V>\<^sub>\<tau> (\<pi>\<^sup>1 (chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))))   (\<pi>\<^sup>2 (  chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))    ))) \<Turnstile> (\<alpha> \<bullet> I) 
                  \<and> I \<inter> \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)) = {}"
      proof -
        assume kIsSuccessor : "(\<exists> e . k = Suc e)"
        have "\<And> e . ((k = Suc e) \<Longrightarrow> (thereIsAnUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))) \<Longrightarrow>
          \<exists>I\<in>\<I>.  (\<V>\<^sub>\<tau> (\<pi>\<^sup>1 (chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))))   (\<pi>\<^sup>2 (  chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))    ))) \<Turnstile> (\<alpha> \<bullet> I) 
                  \<and> I \<inter> \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)) = {})"
        proof -
          fix e
          assume kIsSucE : "k = Suc e"
          show "thereIsAnUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>)) \<Longrightarrow>
         \<exists>I\<in>\<I>. \<V>\<^sub>\<tau> (\<pi>\<^sup>1 (chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>)))) (\<pi>\<^sup>2 (chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>)))) \<Turnstile> \<alpha> \<bullet> I \<and> I \<inter> \<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>) = {}"
          proof -
            (* we know k is a successor, f1(0) is not interesting *)
            
            from kIsSucE have b5392 : "e \<le> k" by arith
            from b5392 seventhGoal stateSetFromRuleSet_def kIsSucE  have usedHyp : 
              "(\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))) 
         = \<Pi>\<^sub>\<phi> ((\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> (\<Union>| (states |`| \<W> n e \<R> \<aa>\<^sub>1)) (\<Union>| (states |`| \<W> n e \<R> \<aa>\<^sub>2)))))" by metis
            assume 0 : "thereIsAnUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))"
            def chosen == "chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))"
            def chosenSide == "\<pi>\<^sup>1 chosen"
            def chosenRule == "\<pi>\<^sup>2 chosen"
              
            have r483 : "chosenRule |\<in>| ((\<W> n k \<R>) chosenSide)" 
              and y71 : "\<not> (realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> chosenSide) chosenRule) (\<alpha> \<bullet> ((\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))) \<union> {[]})))"
            proof -
              from chosen_def chosenUnrealizedRule_def have u2 : "chosen = (SOME x. x \<in> (unrealizedRules (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))))" by auto
              from 0 thereIsAnUnrealizedRule_def u2 someI have u4 : "chosen \<in> (unrealizedRules (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))))" by fast
              from u4 unrealizedRules_def  have u5a: "(\<pi>\<^sup>2 chosen) |\<in>| ((\<W> n k \<R>) (\<pi>\<^sup>1 chosen)) " by auto
              have n76587 : "symbol (\<pi>\<^sup>2 chosen) = \<alpha>" using wSymbol u5a by auto
              from u5a u4 unrealizedRules_def  n76587
              have u5: "(\<pi>\<^sup>2 chosen) |\<in>| ((\<W> n k \<R>) (\<pi>\<^sup>1 chosen)) 
                 \<and> (\<not> (realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> (\<pi>\<^sup>1 chosen)) (\<pi>\<^sup>2 chosen)) (\<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)) \<union> {[]}))))" by auto  
              from u5 chosenSide_def chosenRule_def show  "chosenRule |\<in>| ((\<W> n k \<R>) chosenSide)" by auto
              from u5 chosenSide_def chosenRule_def show  "\<not> realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> chosenSide) chosenRule) (\<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>) \<union> {[]}))" by metis
            qed
              
            from r483 wInR alphaIsTransition have v60 : "symbol chosenRule = \<alpha>" by blast
            from v60 realized_rule_state_reverse   have n6556787 : " (\<And>state. state |\<in>| states chosenRule \<Longrightarrow> realizedIn (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> chosenSide) state) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>))) \<Longrightarrow> realizedIn (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> chosenSide) chosenRule) (\<alpha> \<bullet> ((\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>)) \<union> {[]}))" by auto
            from y71 have "\<not> (realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> chosenSide) chosenRule) (\<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))\<union> {[]})))" by metis
            then have b6567 : "\<not> (realizedIn (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> chosenSide) chosenRule) (\<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)) \<union> {[]})))" using realizedForestTreeRule by auto
                
            have "\<not> (realizedIn (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> chosenSide) chosenRule) (\<alpha> \<bullet> ((\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>)) \<union> {[]})))"
            proof 
              assume "(realizedIn (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> chosenSide) chosenRule) (\<alpha> \<bullet> ((\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>)) \<union> {[]})))"
              then obtain g where b657 : "((g \<in> (\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> chosenSide) chosenRule)))" and b54465 : "(fset (\<Pi> g) \<subseteq> (\<alpha> \<bullet> ((\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>)) \<union> {[]})))" using realizedIn_def by metis
              from b6567 realizedIn_def b657 have "\<not> ((fset (\<Pi> g) \<subseteq> (\<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)) \<union> {[]}  ))))" by metis
              then  show "False"                      using b54465 by auto
            qed
            then obtain badState where b100 : "badState |\<in>| states chosenRule" and b1pre : "\<not> (realizedIn (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> chosenSide) badState) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>)))" using n6556787                  by auto 
                
            from b1pre have b1 : "\<not> (realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> chosenSide) badState) ((\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))))"              by (simp add: realizedForestTreeState) 
                
            def Sa1 == "\<Union>| (states |`| ( (\<W> n e \<R> \<aa>\<^sub>1)))"
            def Sa2 == "\<Union>| (states |`| ( (\<W> n e \<R> \<aa>\<^sub>2)))"
              
            from r483 wInR have b334 : "chosenRule |\<in>| \<R> chosenSide" by blast
            from wInR b100  inStateSet have y85 : "badState |\<in>| state_set (\<A> chosenSide)"
              using b334 by auto 
            from wInR Sa1_def inStateSet have y86 : "Sa1 |\<subseteq>| state_set \<A>\<^sub>1"      by fastforce
            from wInR Sa2_def inStateSet have y87 : "Sa2 |\<subseteq>| state_set \<A>\<^sub>2"  by fastforce
                
                
            from usedHyp Sa1_def Sa2_def have y73 : "\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)) = \<Pi>\<^sub>\<phi> ((\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2)))" by metis
                 
                (* it is enough to know that f1 n k R is a saturation for *some* rule set, it is not important what this rule set is *) 
            from    y85 y86 y87 existsUniformConstant constantIsSuitableForAllStates_def rulesLangsNonempty have y88 : "constantIsSuitableForStates chosenSide badState Sa1 Sa2 \<N>" by metis
            from y88 constantIsSuitableForStates_def obtain I where y82 : "I \<in> \<I>" and invokeLemma2 : "((\<forall> n . ((Suc n > \<N>) \<longrightarrow> ((\<not>(realizedIn 
                                                           (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> chosenSide) badState)  
                                                           (\<Pi>\<^sub>\<delta> (fset (\<Z>\<^sub>\<delta> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2) )))
                                                     ) )
                                                     \<longrightarrow> ( ( ( (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> chosenSide) badState) \<Turnstile> I)
                                                                       \<and> ((I \<inter> \<Pi>\<^sub>\<delta> ((  \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2  ))) = {})
                                                                      )
                                                               )
                                                          )
                                            )))" by metis
            
            then have "\<not> realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> chosenSide) badState) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>))" using \<Z>\<tau>_lemma   b1 y73  realizedForestTreeState realizedForestTreeRule \<Z>\<^sub>\<phi>\<^sub>F_def by auto
            then have r105 : "\<not> realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> chosenSide) badState) (\<Pi>\<^sub>\<phi> ((\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2))))" using \<Z>\<tau>_lemma   b1 y73  realizedForestTreeState realizedForestTreeRule \<Z>\<^sub>\<phi>\<^sub>F_def by auto
            then have y75 : "\<not> (realizedIn (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> chosenSide) badState) (\<Pi>\<^sub>\<phi> ((fset (\<Z>\<^sub>\<phi> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2))))))" using \<Z>\<tau>_lemma   b1 y73  realizedForestTreeState realizedForestTreeRule \<Z>\<^sub>\<phi>\<^sub>F_def by (simp add: \<Z>\<^sub>\<phi>\<Z>\<^sub>\<phi>\<^sub>Flemma)
            from y75 notation_lemma1 have r106 : "\<not> realizedIn (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> chosenSide) badState) (\<Pi>\<^sub>\<delta> (fset (\<Z>\<^sub>\<delta> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2))))" by metis
            from r106 invokeLemma2 nAssum y75 nAssum            have y76 : "( ( ( (\<L>\<^sub>\<tau>\<^sub>\<sigma> (\<A> chosenSide) badState) \<Turnstile> I))) \<and> ((I \<inter> \<Pi>\<^sub>\<delta> ((  \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2  )))= {}) " by metis
                
            have y81 : "I \<inter> \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)) = {}"
            proof -
              have y8085 : "UNION (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2) fset = \<Pi>\<^sub>\<phi> (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2)" using differentPZLemma \<Z>\<tau>_lemma \<Z>\<^sub>\<phi>\<^sub>F_def by auto
              from \<Z>\<^sub>\<phi>\<^sub>F_subset   y76 Int_absorb2 Int_empty_right inf_sup_aci(3) pathsForestLangMonotone 
              have y870 : "I \<inter> \<Pi>\<^sub>\<delta> (  (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2)) = {}" by metis
              then have "I \<inter> \<Pi>\<^sub>\<phi> (( (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2))) = {}" using y8085 by auto
              then have y80 : "I \<inter> \<Pi>\<^sub>\<phi> ((\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2))) = {}" using \<Z>\<tau>_lemma \<Z>\<^sub>\<phi>\<^sub>F_def pathsForestLangMonotone
              proof -
                obtain aas :: "abc list set \<Rightarrow> abc list set \<Rightarrow> abc list" where
                  "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> (\<exists>v3. v3 \<in> x0 \<and> v2 = v3)) = (aas x0 x1 \<in> x1 \<and> (\<exists>v3. v3 \<in> x0 \<and> aas x0 x1 = v3))"
                  by moura
                then obtain aasa :: "abc list set \<Rightarrow> abc list set \<Rightarrow> abc list" where
                  f1: "\<forall>A Aa. (A \<inter> Aa \<noteq> {} \<or> (\<forall>as. as \<notin> A \<or> (\<forall>asa. asa \<notin> Aa \<or> as \<noteq> asa))) \<and> (A \<inter> Aa = {} \<or> aas Aa A \<in> A \<and> aasa Aa A \<in> Aa \<and> aas Aa A = aasa Aa A)"
                  by moura
                then have "aas (\<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2))) I \<notin> I \<or> aasa (\<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2))) I \<notin> \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2)) \<or> aas (\<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2))) I \<noteq> aasa (\<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2))) I"
                  by (meson \<Z>\<^sub>\<phi>\<^sub>F_subset \<open>I \<inter> \<Pi>\<^sub>\<phi> (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2) = {}\<close> pathsForestLangMonotone rev_subsetD)
                then show ?thesis
                  using f1 by meson
              qed (*     by (metis (no_types, lifting) IntD2 \<Z>\<^sub>\<phi>\<^sub>F_subset disjoint_iff_not_equal inf.orderE) *)
              from y80 y73 show "I \<inter> \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)) = {}" by simp
            qed
              
            from b334 alphaIsTransition have b333 : "symbol chosenRule = \<alpha>" by metis
                
            from y76 \<V>\<^sub>\<tau>_def have z2 : "(\<V>\<^sub>\<tau> chosenSide chosenRule) \<Turnstile> (\<alpha> \<bullet> I)"  (* TODO can this replace the rootOfV lemma? *)
            proof -
              from b333 entails_def y76 b100 have y91 : "\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> chosenSide) chosenRule \<subseteq> existential_satisfaction_set (\<alpha> \<bullet> I)"                using entailsStateRule by fastforce 
              from necess_def have  "necess (\<A> chosenSide) \<I> chosenRule = op \<bullet> (symbol chosenRule) ` {i \<in> \<I> . \<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> chosenSide) chosenRule \<subseteq> existential_satisfaction_set (symbol chosenRule \<bullet> i)}" by metis
              then have h655 : "necess (\<A> chosenSide) \<I> chosenRule = op \<bullet> \<alpha> ` {i \<in> \<I>. \<L>\<^sub>\<tau>\<^sub>\<rho>  (\<A> chosenSide) chosenRule \<subseteq> existential_satisfaction_set (\<alpha> \<bullet> i)}" using b333 by metis
              from y82 y91 have y94 : "(\<alpha> \<bullet> I) \<in> (necess (\<A> chosenSide) \<I> chosenRule)" using h655 by blast
              have y96 : "\<V>\<^sub>\<tau> chosenSide chosenRule \<subseteq> existential_satisfaction_set (\<alpha> \<bullet> I)"
              proof
                fix tr
                assume y92 : "tr \<in> \<V>\<^sub>\<tau> chosenSide chosenRule"
                from y92 \<V>\<^sub>\<tau>_def y94 have y95 : "\<Pi> tr \<in>  (image \<Pi> (existential_satisfaction_set (\<alpha> \<bullet> I))   )" by auto
                from y95 lemmaPathExistence show  "tr \<in> existential_satisfaction_set (\<alpha> \<bullet> I)" by auto
              qed
              from entails_def y96 show "entails (\<V>\<^sub>\<tau> chosenSide chosenRule) (\<alpha> \<bullet> I)" by auto
            qed
            from y81 z2 y82 chosenSide_def chosenRule_def chosen_def show "
           \<exists>I\<in>\<I>. \<V>\<^sub>\<tau> (\<pi>\<^sup>1 (chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>)))) (\<pi>\<^sup>2 (chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>)))) \<Turnstile> \<alpha> \<bullet> I \<and> I \<inter> \<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>) = {}" by auto
          qed
        qed
        then show "(\<exists> e . k = Suc e) \<Longrightarrow> (thereIsAnUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))) \<Longrightarrow>
          \<exists>I\<in>\<I>.  (\<V>\<^sub>\<tau> (\<pi>\<^sup>1 (chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))))   (\<pi>\<^sup>2 (  chosenUnrealizedRule (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))    ))) \<Turnstile> (\<alpha> \<bullet> I) 
                  \<and> I \<inter> \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)) = {}" by auto
      qed         
    qed
      
    show firstGoalInner : "(\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) |\<subseteq>| \<ff>\<^sub>1 n k \<R>" (* (a) *)
    proof (induct "k" arbitrary: ks rule: less_induct)
      fix k
      assume hyp1 : "(\<And> y. y < k \<Longrightarrow> (\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) |\<subseteq>| \<ff>\<^sub>1 n y \<R>) "
        
      have firstForZero : "k = 0 \<Longrightarrow> (\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) |\<subseteq>| \<ff>\<^sub>1 n k \<R>"
      proof -
        assume b1 : "k = 0"
        from factoredFInFa0 alphaIsTransition have b3 : "(\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) |\<subseteq>| \<ff>\<^sub>1 n 0 \<R>" by auto
        from b1 b3 show "(\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) |\<subseteq>| \<ff>\<^sub>1 n k \<R>" by simp
      qed
        
      show first : "(\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) |\<subseteq>| \<ff>\<^sub>1 n k \<R>"
      proof (rule disjE)
        show "k = 0 \<or> (\<exists>q . (k = Suc q))" by arith
        from firstForZero show "k = 0 \<Longrightarrow> (\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) |\<subseteq>| \<ff>\<^sub>1 n k \<R>" by auto
        show "(\<exists>e . (k = Suc e)) \<Longrightarrow> (\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) |\<subseteq>| \<ff>\<^sub>1 n k \<R>"
        proof -
          assume i500 : "(\<exists>e . (k = Suc e))"
          from i500 obtain e where i501 : "k = Suc e" by auto
          from hyp1  have previousFirst : "(\<And> k0. (k0 < k \<Longrightarrow> ((\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) |\<subseteq>| \<ff>\<^sub>1 n k0 \<R>)))" using antisym_conv2 by auto
          from fourth have fourthInFifth : "(\<And> y.  (\<exists>e. y = Suc e) \<Longrightarrow>
               thereIsAnUnrealizedRule (\<W> n y \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n y \<R>))) \<Longrightarrow>
               \<exists>I\<in>\<I>. (\<V>\<^sub>\<tau> (\<pi>\<^sup>1 (chosenUnrealizedRule (\<W> n y \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n y \<R>)))))
                                    (\<pi>\<^sup>2 (chosenUnrealizedRule (\<W> n y \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n y \<R>))))))
                          \<Turnstile> (\<alpha> \<bullet> I) \<and>
                          I \<inter> \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n y \<R>)) = {})" using less_Suc_eq by auto
          show "(\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) |\<subseteq>| \<ff>\<^sub>1 n k \<R>"
          proof (rule disjE)
            show "e = 0 \<or> e > 0" by auto
                
            show "e = 0 \<Longrightarrow> \<alpha> \<diamondop> \<ff> (Suc n) \<R> |\<subseteq>| \<ff>\<^sub>1 n k \<R>" 
            proof -
              assume b655687 : "e = 0"
              have "(\<ff>\<^sub>1 n 0 \<R>) = \<Z>\<^sub>\<tau> n UNIV" by simp
              have "\<ff>\<^sub>1 n (Suc 0) \<R> = \<Z>\<^sub>\<tau> n  (\<P>\<^sub>\<sigma> (\<W> n 0 \<R>))"                  using secondGoal by metis
              have "(\<W> n 0 \<R>) = ((\<R> ))" by auto
              then have "\<Z>\<^sub>\<tau> n  (\<P>\<^sub>\<sigma> (\<W> n 0 \<R>)) = \<Z>\<^sub>\<tau> n  (\<P>\<^sub>\<sigma> \<R>)" by auto
              have "\<alpha> \<diamondop> \<ff> (Suc n) \<R>|\<subseteq>| \<Z>\<^sub>\<tau> n  (\<P>\<^sub>\<sigma> \<R>)" 
              proof 
                fix x
                assume "x |\<in>| \<alpha> \<diamondop> \<ff> (Suc n) \<R>"
                then obtain tr where n54576 : "tr |\<in>| \<ff> (Suc n) \<R>" and n67568 : "x |\<in>| childrenSet tr"  using  factorByRootSymbolF_lemma factorByRootSymbol_def                  using notin_fset by fastforce
                then have "tr \<in> \<P> \<R>"                  using zInP by auto
                then have "x \<in> \<P>\<^sub>\<sigma> \<R>" using n67568  approxForRuleAndChildrenStates by auto
                then show "x |\<in>| \<Z>\<^sub>\<tau> n  (\<P>\<^sub>\<sigma> \<R>)" using n67568 n54576                      by (metis \<open>\<ff>\<^sub>1 n 0 \<R> = \<Z>\<^sub>\<tau> n UNIV\<close> \<open>x |\<in>| \<alpha> \<diamondop> \<ff> (Suc n) \<R>\<close> fset_mp hyp1 i500 zIntersectLemma zero_less_Suc)
              qed
              then have "\<alpha> \<diamondop> \<ff> (Suc n) \<R> |\<subseteq>| \<ff>\<^sub>1 n 1 \<R>"                using \<open>\<Z>\<^sub>\<tau> n (\<P>\<^sub>\<sigma> (\<W> n 0 \<R>)) = \<Z>\<^sub>\<tau> n (\<P>\<^sub>\<sigma> \<R>)\<close> \<open>\<ff>\<^sub>1 n (Suc 0) \<R> = \<Z>\<^sub>\<tau> n (\<P>\<^sub>\<sigma> (\<W> n 0 \<R>))\<close> by auto 
              then show "\<alpha> \<diamondop> \<ff> (Suc n) \<R> |\<subseteq>| \<ff>\<^sub>1 n k \<R>" using b655687 i501 by auto
            qed
            show "0 < e \<Longrightarrow> \<alpha> \<diamondop> \<ff> (Suc n) \<R> |\<subseteq>| \<ff>\<^sub>1 n k \<R>"
            proof -
              assume h65678 : "0 < e"
              then obtain e2 where i509 : "e = Suc e2"                  by (metis Suc_pred) 
              have "thereIsAnUnrealizedRule  (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))) \<or> (\<not> (thereIsAnUnrealizedRule  (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)))))" by auto
              show "(\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) |\<subseteq>| \<ff>\<^sub>1 n k \<R>"
              proof (rule ccontr)
                assume "\<not> ((\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) |\<subseteq>| \<ff>\<^sub>1 n k \<R>)"
                then obtain t where b574 : "t |\<in>| ((\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)))" and b575 : "t |\<notin>| \<ff>\<^sub>1 n k \<R>" by blast
                then have b576 : "t |\<in>| \<ff>\<^sub>1 n e \<R>" using previousFirst i501 by blast
                from secondGoal b576 i509 have "t |\<in>| \<Z>\<^sub>\<tau> n (\<P>\<^sub>\<sigma> (\<W> n e2 \<R>))" by metis
                from secondGoal b575 i501 have b6545 : "t |\<notin>| \<Z>\<^sub>\<tau> n (\<P>\<^sub>\<sigma> (\<W> n e \<R>))" by metis
                from b574 have r400 : " (t |\<in>| (\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)))" by auto
                from r400 factorByRootSymbolF_lemma factorByRootSymbol_def 
                obtain p2 where r401 : "(p2 |\<in>| ((\<ff> (Suc n)  \<R>)))" and r402 : "t |\<in>| childrenSet p2" using mem_Collect_eq notin_fset by fastforce  (* p2 = t0 *)
                from r401 r400 fSupportsRules satisfiesApproximatorForRuleSet_def 
                have s502 : "\<forall> i . (\<forall> pi \<in> (pathsInTree p2) . pathSatisfiesApproximatorForRuleSet pi  (\<R> i ) i)" by metis (* g *)
                    
                    (* h *)
                from satisfiesApproximatorForStatesFromRuleSet_def  b6545 \<P>\<^sub>\<sigma>_def
                have s507 : "\<exists> i . (\<exists> pi \<in> (pathsInTree t) . \<not> pathSatisfiesApproximatorForStateFromRuleSet pi  ((\<W> n e \<R>) i) i)" by (smt \<open>t |\<in>| \<Z>\<^sub>\<tau> n (\<P>\<^sub>\<sigma> (\<W> n e2 \<R>))\<close> mem_Collect_eq zIntersectLemma)  
                from s507 obtain i where s8375 : "(\<exists> pi \<in> (pathsInTree t) . \<not> pathSatisfiesApproximatorForStateFromRuleSet pi  ((\<W> n e \<R>) i) i)" by auto (* h *)
                    
                    (* i *)
                from s8375 s507 r402 approximatorChildren have r405 : "\<exists> pi \<in> (pathsInTree p2) . (\<not> pathSatisfiesApproximatorForRuleSet pi  ((\<W> n e \<R>) i) i)" by metis
                from s502 s507 r405 obtain pi (* i *)
                  where g200 : "pi \<in> (pathsInTree p2)" 
                    and s510 : "pathSatisfiesApproximatorForRuleSet pi (\<R> i ) i" 
                    and s511 : "\<not> pathSatisfiesApproximatorForRuleSet pi  ((\<W> n e \<R>) i) i" by metis (* i *)
                    
                    (* j *)
                from s510 pathSatisfiesApproximatorForRuleSet_def have s512 : "(\<exists> r  . (hd r |\<in>| (\<R> i)) \<and> (pathFitsListAndListIsARun i pi r))" by metis
                    
                    
                from s511 pathSatisfiesApproximatorForRuleSet_def have s513 : "\<not> (\<exists> r  . (hd r |\<in>| ((\<W> n e \<R>) i)) \<and> (pathFitsListAndListIsARun i pi r))" by metis
                from s512 s513 obtain run where s514 : "(hd run |\<in>| (\<R> i))" and  s515 : "(pathFitsListAndListIsARun i pi run)" and s516 : "(hd run |\<notin>| ((\<W> n e \<R>) i))" by metis
                def r0 == "hd run" (* rho *)
                  
                  (* k *)
                from r0_def s514 s516 have z220 : "r0 |\<in>| (\<R> i) |-| ((\<W> n e \<R>) i)" by (simp add: fminusI) 
                    
                    (* l *)
                    (* now we have an evil path and an evil rule *)
                from r0_def s514 s516 ruleWentMissing obtain k0 
                  where i1 : "k0 < e"
                    and i2 : "r0 |\<in>| ((\<W> n k0 \<R>) i)" 
                    and i3 : "\<not> (r0 |\<in>| ((\<W> n (Suc k0) \<R>) i))" 
                    and i10 : "chosenUnrealizedRule (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k0 \<R>))) = (i,r0)" 
                    and i11 : "(i,r0) \<in> (unrealizedRules (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k0 \<R>))))"
                  by metis
                from i10 have i20 : "i = (\<pi>\<^sup>1 (chosenUnrealizedRule (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k0 \<R>)))))" by (simp add: fst_conv)
                from i10 have i21 : "r0 = (\<pi>\<^sup>2 (chosenUnrealizedRule (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k0 \<R>)))))" by (simp add: snd_conv)
                    
                    (* recall the fourth goal *)
                from  i11 have k0IsSuccessor : "\<exists>e. k0 = Suc e"
                proof -
                  have j4657 : "k0 = 0 \<Longrightarrow> (\<ff>\<^sub>1 n k0 \<R>) = \<Z>\<^sub>\<tau> n UNIV" by simp
                  from realizedInUniv nAssum   rulesLangsNonempty have j4658 : "\<And> r \<ii>. r |\<in>| rule_set (\<A> \<ii>) \<Longrightarrow> symbol r = \<alpha> \<Longrightarrow> ((realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>) r) (\<alpha>  \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> n UNIV) \<union> {[]}))))" by auto 
                  from s514 r0_def have j4659 : "r0 |\<in>| rule_set (\<A> i) \<and> symbol r0 = \<alpha>" using assms by metis
                  have "k0 = 0 \<Longrightarrow> (i,r0) \<notin> (unrealizedRules (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k0 \<R>))))"
                  proof -
                    from j4658 j4659 j4657 have "k0 = 0 \<Longrightarrow> ((realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) r0) (\<alpha>  \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k0 \<R>)) \<union> {[]}))))"  by metis
                    then show "k0 = 0 \<Longrightarrow> (i,r0) \<notin> (unrealizedRules (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k0 \<R>))))" using unrealizedRules_def j4659 by blast
                  qed
                  then have "k0 = 0 \<Longrightarrow> False" using i11 by arith
                  then show "\<exists>e. k0 = Suc e" by arith
                qed
                  
                  (* n *)
                from fourthInFifth i20 i21 k0IsSuccessor have i3 : "(thereIsAnUnrealizedRule (\<W> n k0 \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k0 \<R>)))) \<Longrightarrow>
                                                       \<exists>I\<in>\<I>. (\<V>\<^sub>\<tau> i r0) \<Turnstile> (\<alpha> \<bullet> I) \<and> I \<inter> \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k0 \<R>)) = {}"
                  by metis
                    (* check its conditions *)
                then have i2630 : 
                  "(\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n (Suc k0) \<R>)) 
                           = \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> (stateSetFromRuleSet (\<W> n k0 \<R> \<aa>\<^sub>1)) (stateSetFromRuleSet (\<W> n k0 \<R> \<aa>\<^sub>2)))))" using i1 seventhGoal by metis
                from i2630 stateSetFromRuleSet_def have i4a : 
                  "(\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n (Suc k0) \<R>)) 
                            = \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> (\<Union>| (states |`| \<W> n k0 \<R> \<aa>\<^sub>1))
                                              (\<Union>| (states |`| \<W> n k0 \<R> \<aa>\<^sub>2)))))" by metis
                  
                from aux50 i4a have i4 :
                  "(\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n (Suc k0) \<R>)) 
                            = \<Pi>\<^sub>\<tau>\<^sub>F ((\<Union>| (\<Z>\<^sub>\<phi> n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> (\<Union>| (states |`| \<W> n k0 \<R> \<aa>\<^sub>1))
                                                   (\<Union>| (states |`| \<W> n k0 \<R> \<aa>\<^sub>2)))))))" by metis                
                  (* now have concluded existence of I *)
                from thereIsAnUnrealizedRule_def i11 i3 i4 obtain I 
                  where j300 : "I \<in> \<I>" 
                    and j301 : "(\<V>\<^sub>\<tau> i r0) \<Turnstile> (\<alpha> \<bullet> I)" 
                    and j302 : "I \<inter> \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k0 \<R>)) = {}" by auto
                    (* done with n *)      
                    
                    (* now we need to get the contradiction *)
                    (* show that \<ff> entails I from j300, j301 *)
                from pathsInTree_def s511 g200 have s506 : "pi \<noteq> []" using list.distinct(1) mem_Collect_eq by blast  
                have s507 : "run \<noteq> []" by (metis neq_Nil_conv nonMatching s506 s515)
                def a == "hd pi"
                from r0_def have "r0 = hd run" by auto
                from s506 s507 a_def have s509 : "(( (down a)) \<in> ( \<V>\<^sub>\<tau> i r0  )   )"
                proof -                                 
                  from s515 have y600 : "(pathFitsListAndListIsARun i pi run)" by auto
                  from a_def s506 obtain b where c605 : "pi = (a#b)" by (metis list.collapse) 
                  from s507 obtain c d where y601 : "run = (c#d)" by (metis neq_Nil_conv)
                  from y601 r0_def have c602 : "c = r0" by (simp add: list.sel(1)) 
                  from c605 r0_def a_def pathFitsListAndListIsARunImpliesV s515 s506 s507 c602 show "(( (down a)) \<in> ( \<V>\<^sub>\<tau> i r0  )   ) " by metis
                qed
                from \<V>\<^sub>\<tau>_def s509 have s510 : "(((down a)) \<in> ( \<V>\<^sub>\<tau> i r0  )   )" using mem_Collect_eq by auto 
                from s514 z220 r0_def have s508 : "(hd run) |\<in>| (\<R> i |-| ((\<W> n e \<R>) i))" by simp 
                    (* t is a tree that should represent ONE child of something in \<gg> *)
                have s511 : "(down a) = p2"
                proof -
                  from pathsInTree_def g200 show u600 : "(down a = p2)"
                  proof -
                    have "isAPathp pi \<and> (\<exists>n ns. pi = n # ns \<and> down n = p2)" (*isNodeIn n p2 \<and> isRootNode n)"*)
                      using g200 pathsInTree_def by auto
                    then show ?thesis
                      using a_def by force
                  qed
                qed
                from s510 s511 have s513 : "p2 \<in> ( \<V>\<^sub>\<tau> i r0  )" by metis
                from s513 j301 entails_altdef r401 pathsIntersectionLangTree have i22 : "(\<alpha> \<bullet> I) \<inter> \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n)  \<R>)) \<noteq> {}" by (metis r401) 
                from i1 i501 have i1b :  "k0 \<le> k" by arith
                    (* show that \<ff> does not entail I from j302 *)
                from  i1b i1 previousFirst factorByRootSymbolF_lemma fset_rev_mp notin_fset subsetI 
                have  hypFaOverF : "(\<alpha> \<diamondop> ( (\<ff> (Suc n)  \<R>)) |\<subseteq>| ( (\<ff>\<^sub>1 n k0 \<R>)))" by (simp add: i501 less_SucI)
                have i11 : "(\<alpha> \<bullet> I) \<inter> \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n)  \<R>)) = {}"
                proof (rule ccontr)
                  assume j310 : "\<not> ((\<alpha> \<bullet> I) \<inter> \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n)  \<R>)) = {})"
                  from j310 obtain pi0 where j311 : "pi0 \<in> (\<alpha> \<bullet> I)" and j312 : "pi0 \<in> \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n)  \<R>))" by blast
                  from prefixLetter_def j311 obtain tail where j313 : "pi0 = \<alpha>#tail" by blast
                  from j311 j313 have j315 : "tail \<in> I" using imageE list.inject prefixLetter_def by auto 
                  then have h65787 : "tail \<noteq> []" using j300 emptyPathNotInI by auto
                  from j302 have t500 : "I \<inter> \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k0 \<R>)) = {}" by metis
                  have t316 : "pi0 \<notin> \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n)  \<R>))"
                  proof -
                    from hypFaOverF have t504 : "(\<alpha> \<diamondop> ((\<ff> (Suc n)  \<R>)) |\<subseteq>| ((\<ff>\<^sub>1 n k0 \<R>)))" by auto
                    from j313 j312 pathsOfFactorDown h65787 have j314 : "tail \<in> \<Pi>\<^sub>\<tau> (\<alpha> \<diamondop>\<tau>\<lambda> (fset (\<ff> (Suc n)  \<R>)))"
                    proof -
                      have "hd tail # tl tail = tail"                        by (meson h65787 hd_Cons_tl)
                      then show ?thesis                        by (metis (full_types) j312 j313 pathsOfFactorDown)
                    qed
                    have pathsIneq : "\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n)  \<R>)) \<subseteq> (\<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k0 \<R>)) \<union> {[]} ))" 
                    proof
                      fix x
                      assume h653 : "x \<in> \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n)  \<R>))"
                      from alphaIsTransition fRoot have u6598 : "\<And> tr . tr |\<in>| ((\<ff> (Suc n)  \<R>)) \<Longrightarrow> root tr = \<alpha>" by metis
                      have "\<exists> tail. x = \<alpha>#tail" proof -
                        from h653 pathsForTreeLanguage_def have "x \<in> {p . (\<exists> t \<in>  (fset ((\<ff> (Suc n)  \<R>))) . p |\<in>| \<Pi> t)}" by auto
                        then  obtain y where n100 : "x |\<in>| \<Pi> y" and n101 : "y \<in> (fset (\<ff> (Suc n)  \<R>))" by blast
                        from u6598 n101 have "root y = \<alpha>"
                          by (meson notin_fset) 
                        then show "\<exists> tail. x = \<alpha>#tail" using  \<Pi>.simps n100 root.simps                          using noEmptyPathsInPi by fastforce
                      qed
                      then obtain tail where h654 : "x = \<alpha>#tail" by blast
                      from h653 h654 have h655 : "tail \<in> \<Pi>\<^sub>\<tau>\<^sub>F (\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) \<union> {[]}"                        using factorByRootSymbolF_lemma(2) pathsOfFactorDown                        by (metis IntI empty_iff j314 j315 less_eq_fset.rep_eq pathsTreeLangMonotone subsetCE t500 t504) 
                      from i501 i1 hyp1 have "(\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) |\<subseteq>| \<ff>\<^sub>1 n k0 \<R> " by auto
                      then have "tail \<in> (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k0 \<R>))) \<union> {[]}" using  h655 less_eq_fset.rep_eq pathsTreeLangMonotone subsetCE                        by (metis UnCI UnE)
                      then have "\<alpha>#tail \<in> (\<alpha> \<bullet> ((\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k0 \<R>))) \<union> {[]} ))" using prefixLetter_def by blast
                      then show "x \<in> (\<alpha> \<bullet> ((\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k0 \<R>)))\<union> {[]}))" using h654 by metis
                    qed
                    from t500 j315 have t2832 : "tail \<notin> \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k0 \<R>))" by blast
                    then have n64768 : "\<alpha>#tail \<notin> (\<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k0 \<R>))))" using imageE list.inject prefixLetter_def by auto
                    have  "\<alpha>#tail \<notin> \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n)  \<R>))" 
                    proof (rule ccontr)
                      assume k556i87 : "\<not> (\<alpha>#tail \<notin> \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n)  \<R>)))" 
                      hence "\<alpha>#tail \<in> \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n)  \<R>))" by auto
                      hence "\<alpha>#tail \<in>(\<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k0 \<R>)) \<union> {[]} ))" using pathsIneq                            by auto
                      hence "tail \<in> (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k0 \<R>)) \<union> {[]} )" using prefixLetter_def                        by auto 
                      hence "\<alpha>#tail \<in>(\<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k0 \<R>))))"                            by (simp add: h65787 t2832) 
                      then show "False" using n64768 by auto
                    qed
                    then show "pi0 \<notin> \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n)  \<R>))" using j313 by metis
                  qed
                  from j312 t316 show "False" by metis
                qed
                  (* get contradiction *)
                from fNotEmpty have i21 : "fset (\<ff> (Suc n)  \<R>) \<noteq> {}" by auto
                from i11 i22 show "False" by auto
              qed
            qed
          qed
        qed   
      qed
    qed
  qed
    
    
    
    (*    
    have "(\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) |\<subseteq>| \<ff>\<^sub>1 n (Suc e) \<R>"
    proof -
      from hyp1 hyp5 lessI i501 have c1 : "\<And> l . (\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) |\<subseteq>| \<ff>\<^sub>2 n (Suc e) l \<R>" by metis
      have c3 : "\<not> ((\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) |\<subseteq>| \<ff>\<^sub>1 n (Suc e) \<R>) \<Longrightarrow> False"
      proof -
        assume d1 : "\<not> ((\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) |\<subseteq>| \<ff>\<^sub>1 n (Suc e) \<R>)"
        from d1 have d2 : "\<exists> q . q |\<in>| (\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) \<and> (\<not> (q |\<in>| \<ff>\<^sub>1 n (Suc e) \<R>))" by auto
        from d2 obtain q where d2b : "q |\<in>| (\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) \<and> (\<not> (q |\<in>| \<ff>\<^sub>1 n (Suc e) \<R>))" by metis
        from fInterToSets faInFb fa_def2 d2b  nat_le_linear have d3 : "\<exists> j. q |\<in>| (\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) \<and> (\<not> (q |\<in>| \<ff>\<^sub>2 n (Suc e) j \<R>))"  proof -
           (*from fInterToSets have d21 : "fset (fInter (\<lambda>j.(\<ff>\<^sub>2 n (Suc e) j \<R>))) = (\<Inter> j. fset (\<ff>\<^sub>2 n (Suc e) j \<R>))" by metis*)
           from fa_def2 fInterToSets have d22 : "fset (\<ff>\<^sub>1 n (Suc e) \<R>) = (\<Inter> j. fset (\<ff>\<^sub>2 n (Suc e) j \<R>))" by metis
           from d2b have d20 : "(\<not> (q |\<in>| \<ff>\<^sub>1 n (Suc e) \<R>))" by metis
           (*from d20 d22 have d23 : "\<exists> j. (\<not> (q \<in> fset (\<ff>\<^sub>2 n (Suc e) j \<R>)))" by (simp add: INT_I notin_fset)*)
           from d20 d22  have d24 : "\<exists> j.(\<not> (q |\<in>| \<ff>\<^sub>2 n (Suc e) j \<R>))" by (simp add: notin_fset)
           from d2b d24 show "\<exists> j. q |\<in>| (\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) \<and> (\<not> (q |\<in>| \<ff>\<^sub>2 n (Suc e) j \<R>))" by metis
        qed
        from c1 d3 show "False" by blast
      qed
      
      from c3 i501 show "(\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) |\<subseteq>| \<ff>\<^sub>1 n (Suc e) \<R>" by auto
     qed
    then show "(\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) |\<subseteq>| \<ff>\<^sub>1 n k \<R>" using i501 by auto
    qed
   (* ------------------------------------- *)
  qed
   *)
    
    
  have toShowMain : "(\<not>(\<exists> k. (\<ff>\<^sub>1 n k \<R>) = {||})) \<Longrightarrow> (\<And>k. 
  (\<And>k0. k0 \<ge> k  \<Longrightarrow> (\<W> n (Suc k0) \<R>) = (\<W> n k0 \<R>)    ) \<Longrightarrow>
       (\<alpha> \<bullet> (( \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n (Suc (Suc k)) \<R>)) \<union> {[]})) =  \<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> (Suc n) \<R>))))"
  proof -
    
    fix k
    assume "(\<not>(\<exists> k. (\<ff>\<^sub>1 n k \<R>) = {||}))"
    hence f1NeverEmpty : "\<And>k . (\<ff>\<^sub>1 n k \<R>) \<noteq> {||}" by auto
        
      (* Other inclusion: from first goal *)
    from firstGoal have from_first : "(\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) |\<subseteq>| (\<ff>\<^sub>1 n (Suc k) \<R>)" by metis
        (* One inclusion: calculation *)
    assume h65 : "(\<And>k0. k0 \<ge> k  \<Longrightarrow> (\<W> n (Suc k0) \<R>) = (\<W> n k0 \<R>)    )"
    have "Suc k \<ge> k" by arith 
    then have f3951 : "(\<W> n k \<R>) = (\<W> n (Suc k) \<R>)" and f3952 : "(\<W> n (Suc k) \<R>) = (\<W> n (Suc (Suc k)) \<R>)" using h65 by auto
        
    from f3951 wStationaryLemma have f1 : "\<not> (thereIsAnUnrealizedRule  (\<W> n k \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))))" by auto
    from f3952 wStationaryLemma have f1b : "\<not> (thereIsAnUnrealizedRule  (\<W> n (Suc k) \<R>) (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n (Suc k) \<R>))))"  by blast
        
    show "(\<alpha> \<bullet> ( \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n (Suc (Suc k)) \<R>))\<union> {[]}) =  \<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> (Suc n) \<R>)))"
    proof
      from f3951 secondGoal have f1HasNotChangedAnyMore : "(\<ff>\<^sub>1 n (Suc (Suc k)) \<R>) = (\<ff>\<^sub>1 n (Suc k) \<R>)" by metis
      from f3952 secondGoal have f1HasNotChangedAnyMore2 : "(\<ff>\<^sub>1 n (Suc (Suc (Suc k))) \<R>) = (\<ff>\<^sub>1 n (Suc (Suc k)) \<R>)" by metis
          
      have h76568 : "\<And> \<ii> r . r |\<in>| ((\<W> n (Suc k) \<R>) \<ii>) \<Longrightarrow> symbol r = \<alpha>" using wSymbol by blast
      from f1b thereIsAnUnrealizedRule_def unrealizedRules_def h76568
      have f2 : "\<not> (\<exists> \<ii>. (\<exists> r . ( r |\<in>| ((\<W> n (Suc k) \<R>) \<ii>) \<and> (\<not> (realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>) r) (\<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n (Suc k) \<R>)) \<union> {[]})))))))" by blast 
      from f2 have f3 : "\<And> \<ii>. \<And> r. (r |\<in>| ((\<W> n (Suc k) \<R>) \<ii>) \<Longrightarrow> (realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>) r) (\<alpha> \<bullet> ((\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n (Suc k) \<R>)) \<union> {[]})))))" by metis
          
          
      have allRealized : "\<And> \<ii>. \<And> state. (state |\<in>| (stateSetFromRuleSet (\<W> n (Suc k) \<R> \<ii>)) \<Longrightarrow> (realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>) state) ((\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n (Suc k) \<R>))))))" 
      proof -
        fix \<ii>
        fix state
        assume y1 : "state |\<in>| (stateSetFromRuleSet (\<W> n (Suc k) \<R> \<ii>))"
        from fimageE stateSetFromRuleSet_def y1 ffUnionLemma obtain r where f6 : "r |\<in>| \<W> n (Suc k) \<R> \<ii>" and f7 : "state |\<in>| states r" by metis
        from f6 wSymbol have u765676 : "symbol r = \<alpha>" by blast
        from realizedForestTreeState  realizedForestTreeRule  realized_rule_state  f3 f6 f7 f7 u765676 show "(realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>) state) ((\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n (Suc k) \<R>)) )))" by metis
      qed
        
      def pifan == "\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n (Suc ( k)) \<R>))"
        
      have b5392 : "k \<le> k" by arith
      from seventhGoal pifan_def f3951
      have y300 : "pifan = \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> (stateSetFromRuleSet (\<W> n (Suc k) \<R> \<aa>\<^sub>1))   (stateSetFromRuleSet (\<W> n (Suc k) \<R> \<aa>\<^sub>2))))" by metis
          (* here apply the realization lemma *)
      from allRealized realizationLemma dist_intersectionLanguageOplus_def \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>_def have q2 : 
        "pifan = \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma> (stateSetFromRuleSet (\<W> n (Suc k) \<R> \<aa>\<^sub>1))   (stateSetFromRuleSet (\<W> n (Suc k) \<R> \<aa>\<^sub>2))))"
      proof -
        def S1 == " ( ((\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<aa>\<^sub>1)) |`| (stateSetFromRuleSet (\<W> n (Suc k) \<R> \<aa>\<^sub>1))))"
        def S2 == " ( ((\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<aa>\<^sub>2)) |`| (stateSetFromRuleSet (\<W> n (Suc k) \<R> \<aa>\<^sub>2))))"
        from stateLanguagesClosedArbitraryOplus S1_def have y5555 : "\<forall>l . l |\<in>| S1 \<longrightarrow> closedUnderArbitraryPlus (l)" using fimageE by blast 
        from stateLanguagesClosedArbitraryOplus S2_def have y5556 : "\<forall>l . l |\<in>| S2 \<longrightarrow> closedUnderArbitraryPlus (l)" using fimageE by blast 
        def fTree == "\<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n ( ((\<Psi>\<^sub>\<phi> ` (\<Uplus> ( S1))) \<inter> (\<Psi>\<^sub>\<phi> `(\<Uplus> ( S2))))))"
        from fTree_def y300 S1_def S2_def \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>_def \<A>.simps have fTreePi : "fTree = pifan"
        proof -
          from S1_def S2_def \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>_def aut_def have b380 : "(( \<Psi>\<^sub>\<phi> ` (\<Uplus> (S1))) \<inter> (\<Psi>\<^sub>\<phi> `  (\<Uplus> (S2)))) 
                          = (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> (stateSetFromRuleSet (\<W> n (Suc k) \<R> \<aa>\<^sub>1))   (stateSetFromRuleSet (\<W> n (Suc k) \<R> \<aa>\<^sub>2)))"  by metis
          from b380 fTree_def y300 show ?thesis by metis
        qed
        have realizedDistr : "\<And> x z.(realizedInForest x z \<Longrightarrow> realizedInForest (distEquivalenceClassForests x) z)" by (metis (mono_tags, lifting) distEquivalenceClassForests_def mem_Collect_eq realizedInForest_def) 
            
        from fimageE  allRealized pifan_def
        have allRealizedPi2 : "\<And> \<ii> l. (l |\<in>| ( ((\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>)) |`| (stateSetFromRuleSet (\<W> n (Suc k) \<R> \<ii>)))) 
                                                     \<Longrightarrow> (realizedInForest l pifan))" by metis
        have caseOt : "(\<And> \<ii>. (\<ii> = \<aa>\<^sub>1 \<or> \<ii> = \<aa>\<^sub>2))" using \<A>.cases by auto
        from realizedDistr allRealizedPi2 S1_def S2_def have y5551 : "\<And> l. (l |\<in>| (S1) \<Longrightarrow> realizedInForest l  pifan)" using fimageE by blast 
        from realizedDistr allRealizedPi2 S1_def S2_def have  y5561 : "\<And> l. (l |\<in>| (S2) \<Longrightarrow> realizedInForest l pifan)" using fimageE by blast 
        from y5551 y5561 fTreePi have y5551a : "\<And> l. (l |\<in>| (S1) \<Longrightarrow> realizedInForest l fTree)" and y5561a : "\<And> l. (l |\<in>| (S2) \<Longrightarrow> realizedInForest l fTree)" by auto 
        
        from statesLanguagesNonempty S1_def S2_def wInR stateSetFromRuleSet_def  have h6588 : "\<And> r \<ii> s. r |\<in>| (\<W> n (Suc k) \<R> \<ii>)  \<Longrightarrow> s |\<in>| states r \<Longrightarrow> \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>) s \<noteq> {}" by blast
            
        have nonempty500 : "(\<forall>l. l |\<in>| S1 \<longrightarrow> l \<noteq> {}) \<and>  ( \<forall>l. l |\<in>| S2 \<longrightarrow> l \<noteq> {})"
        proof 
          have n567687 : "\<And> s l. (s = S1 \<or> s=S2) \<Longrightarrow> l |\<in>| s \<longrightarrow> l \<noteq> {}"
          proof 
            fix s l
            assume a90 : "(l :: abc tree fset set) |\<in>| s"
            assume a91 : "s = S1 \<or> s=S2"
            then obtain i where "s = \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) |`| stateSetFromRuleSet (\<W> n (Suc k) \<R> i)" using S1_def S2_def                  by blast
            hence "s = \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) |`| (\<Union>| (states |`| (\<W> n (Suc k) \<R> i)))" using stateSetFromRuleSet_def by metis
            then obtain state where a94 : "l = \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) state" and "state |\<in>| (\<Union>| (states |`| (\<W> n (Suc k) \<R> i)))" using a90 by blast
            then obtain rule where a93 : "state |\<in>| states rule" and a92 : "rule |\<in>| (\<W> n (Suc k) \<R> i)"                    by auto 
            from h6588  show "l \<noteq> {}"                  using    a92 a93 a94              by blast 
          qed
          from n567687 show "\<forall>l. l |\<in>| S1 \<longrightarrow> l \<noteq> {}" by auto
          from n567687 show "\<forall>l. l |\<in>| S2 \<longrightarrow> l \<noteq> {}" by auto
        qed
          
          
        have noEmptyForests1 : "(\<And>l forest. l |\<in>| S1 \<Longrightarrow> forest \<in> l \<Longrightarrow> forest \<noteq> {||}) " using S1_def noEmptyForests by metis
    have noEmptyForests2 : "(\<And>l forest. l |\<in>| S2 \<Longrightarrow> forest \<in> l \<Longrightarrow> forest \<noteq> {||})" using S2_def noEmptyForests by metis
          
        from realizationLemma  y5555 y5556 nonempty500 noEmptyForests1 noEmptyForests2
        have u702 : "(\<And> l. l |\<in>| S1 \<Longrightarrow> realizedInForest l (\<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n ((\<Psi>\<^sub>\<phi> ` (\<Uplus> ( S1))) \<inter> (\<Psi>\<^sub>\<phi> ` (\<Uplus> ( S2))))))) \<Longrightarrow>
                         (\<And> l. l |\<in>| S2 \<Longrightarrow> realizedInForest l (\<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n ((\<Psi>\<^sub>\<phi> ` (\<Uplus> ( S1))) \<inter> (\<Psi>\<^sub>\<phi> ` (\<Uplus> ( S2))))))) \<Longrightarrow>
                           \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n ((\<Psi>\<^sub>\<phi> ` (\<Uplus> ( S1))) \<inter> (\<Psi>\<^sub>\<phi> ` (\<Uplus> ( S2))))) 
                           = \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n ((\<Psi>\<^sub>\<phi> ` (\<Oplus> ( S1))) \<inter> (\<Psi>\<^sub>\<phi> ` (\<Oplus> ( S2)))))" by blast
        from fTreePi fTree_def nonempty500 u702 y5555 y5556 y5551a y5561a S1_def S2_def fTreePi fTree_def 
        have y5571 : "fTree = \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n ((\<Psi>\<^sub>\<phi> `(\<Oplus> ( S1))) \<inter> (\<Psi>\<^sub>\<phi> `(\<Oplus> ( S2)))))" by metis
        from  fTreePi  y5571
        have y5572 : "pifan =  \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n ((\<Psi>\<^sub>\<phi> `(\<Oplus> ( S1))) \<inter> (\<Psi>\<^sub>\<phi> `(\<Oplus> ( S2)))))" by metis
        from aut_def dist_intersectionLanguageOplus_def 
        have y5573 : "\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma> (stateSetFromRuleSet (\<W> n (Suc k) \<R> \<aa>\<^sub>1))   (stateSetFromRuleSet (\<W> n (Suc k) \<R> \<aa>\<^sub>2)) 
                        =  (\<Psi>\<^sub>\<phi> ` (\<Oplus> ((\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<aa>\<^sub>1)) |`| (stateSetFromRuleSet (\<W> n (Suc k) \<R> \<aa>\<^sub>1))))) 
                         \<inter> (\<Psi>\<^sub>\<phi> `((\<Oplus> ( ((\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<aa>\<^sub>2)) |`| (stateSetFromRuleSet (\<W> n (Suc k) \<R> \<aa>\<^sub>2)))))))" by metis
        from y5572 y5573 S1_def S2_def show ?thesis by metis
      qed
      have "\<And>i. (\<W> n (Suc k) \<R> i) |\<subseteq>| (\<R> i)" using wInR by blast 
          
          
      from f1NeverEmpty  obtain tree where n654765 : "tree |\<in>| (\<ff>\<^sub>1 n (Suc (Suc ( k))) \<R>)" by blast
          
          
      have "tree = (NODE (root tree) (childrenSet tree))"
        by (metis childrenSet.elims root.simps) 
      hence "[root tree] |\<in>| \<Pi> tree" using rootIsPath by metis
      hence "[root tree] \<in> \<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n (Suc (Suc ( k))) \<R>)" using n654765 pathsForTreeLanguage_def
        by (metis (mono_tags, lifting) mem_Collect_eq notin_fset) 
      hence "[root tree] \<in> \<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n (Suc ( ( k))) \<R>)" using  \<ff>\<^sub>1.simps(2)            using f1HasNotChangedAnyMore by auto 
      hence n655876 : "[root tree] \<in> pifan" using pifan_def by auto
      hence "[root tree] \<in> \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma> (stateSetFromRuleSet (\<W> n (Suc k) \<R> \<aa>\<^sub>1))   (stateSetFromRuleSet (\<W> n (Suc k) \<R> \<aa>\<^sub>2))))"    using q2 by auto
      then obtain forest where n76443544 : "forest \<in> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma> (stateSetFromRuleSet (\<W> n (Suc k) \<R> \<aa>\<^sub>1))   (stateSetFromRuleSet (\<W> n (Suc k) \<R> \<aa>\<^sub>2))))" 
        and n654654 : "[root tree] |\<in>|  pathsInForest forest" using pathsForForestLanguage_def by blast
      from n654654 have "\<exists> tree . tree |\<in>| forest" using pathsInForest_def ffUnionLemma
        by (metis pathsTreeForest) 
      hence n443876545 : "\<exists> forest . (forest \<in> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma> (stateSetFromRuleSet (\<W> n (Suc k) \<R> \<aa>\<^sub>1))   (stateSetFromRuleSet (\<W> n (Suc k) \<R> \<aa>\<^sub>2)))) \<and> forest \<noteq> fempty)" using n76443544 by auto
      have "(\<And>\<ii> rule. rule |\<in>| (\<W> n (Suc k) \<R> \<ii>) \<Longrightarrow> symbol rule = \<alpha>)" using wSymbol  by blast
          
      have n764654 :  "pathsInTree tree \<noteq> {}" using theSingletonPathExists by blast
          
      from n654765 \<ff>\<^sub>1.simps  have "tree |\<in>|  inf_fset2 (\<ff>\<^sub>1 n (Suc k) \<R>) (\<P>\<^sub>\<sigma> (\<W> n (Suc k) \<R>)) " by auto
      hence  "tree \<in>  (\<P>\<^sub>\<sigma> (\<W> n (Suc k) \<R>)) "            by (metis Int_iff inf_fset2.rep_eq notin_fset) 
      hence "\<And> \<ii> . (\<forall> p \<in> (pathsInTree tree) . 
             pathSatisfiesApproximatorForStateFromRuleSet p ((\<W> n (Suc k) \<R>) \<ii>) \<ii>)" using \<P>\<^sub>\<sigma>_def satisfiesApproximatorForStatesFromRuleSet_def by blast
      hence "\<And> \<ii> . (pathsInTree tree = {} \<or> (\<exists>rule. rule |\<in>| (\<W> n (Suc k) \<R> \<ii>)))" using pathSatisfiesApproximatorForStateFromRuleSet_def
      proof -
        fix \<ii> :: ot
        assume "\<And>\<ii>. \<forall>p\<in>pathsInTree tree. pathSatisfiesApproximatorForStateFromRuleSet p (\<W> n (Suc k) \<R> \<ii>) \<ii>"
        then show "pathsInTree tree = {} \<or> (\<exists>r. r |\<in>| \<W> n (Suc k) \<R> \<ii>)"
          by (meson notin_fset pathSatisfiesApproximatorForStateFromRuleSet_def theSingletonPathExists)
      qed
      hence nuy53676 : "\<And> \<ii> . (\<exists>rule. rule |\<in>| (\<W> n (Suc k) \<R> \<ii>))" using n764654 by auto
          
          
          
      from psiRulesStatesLemma nuy53676 have "(\<And>\<ii> rule. rule |\<in>| (\<W> n (Suc k) \<R> \<ii>) \<Longrightarrow> symbol rule = \<alpha>) \<Longrightarrow>
  (\<And>i. \<exists>rule. rule |\<in>| (\<W> n (Suc k) \<R> i)) \<Longrightarrow>
  \<exists>forest. forest \<in> \<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<W> n (Suc k) \<R> \<aa>\<^sub>1) (\<W> n (Suc k) \<R> \<aa>\<^sub>2)) \<and> forest \<noteq> {||} \<Longrightarrow>
  \<alpha> \<bullet> (\<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma> (stateSetFromRuleSet (\<W> n (Suc k) \<R> \<aa>\<^sub>1)) (stateSetFromRuleSet (\<W> n (Suc k) \<R> \<aa>\<^sub>2)))) \<union> {[]}) = \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F (Suc n) (\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<W> n (Suc k) \<R> \<aa>\<^sub>1) (\<W> n (Suc k) \<R> \<aa>\<^sub>2)))"
        using n443876545 by blast 
      
      
      
              
      have psiRulesStates : 
        "\<alpha> \<bullet> (\<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<Oplus>\<^sub>\<sigma> (stateSetFromRuleSet (\<W> n (Suc k) \<R> \<aa>\<^sub>1))   (stateSetFromRuleSet (\<W> n (Suc k) \<R> \<aa>\<^sub>2))))   \<union> {[]})
              = (\<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F (Suc n) ((\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (((\<W> n (Suc k) \<R>) \<aa>\<^sub>1))((((\<W> n (Suc k) \<R>) \<aa>\<^sub>2)))))))" using wSymbol psiRulesStatesLemma f1NeverEmpty q2 n443876545
        by (meson nuy53676)
        
          
          
      from q2 psiRulesStates      have q1 : "\<alpha> \<bullet>  (pifan\<union> {[]}) = (\<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F (Suc n) ((\<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (((\<W> n (Suc k) \<R>) \<aa>\<^sub>1))((((\<W> n (Suc k) \<R>) \<aa>\<^sub>2)))))))" by metis
          
          
          
          
      from paths_monoForest q1 z_mono uplusInOplus \<Psi>\<^sub>\<Sigma>\<^sub>\<rho>_def dist_intersectionLanguageOplusRules_def 
      have q3 : "\<alpha> \<bullet>  (pifan\<union> {[]}) \<subseteq> \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F (Suc n) ((\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (((\<W> n (Suc k) \<R>) \<aa>\<^sub>1))((((\<W> n (Suc k) \<R>) \<aa>\<^sub>2))))))"
      proof -
        from uplusInOplus 
        have q851 : "((\<Psi>\<^sub>\<phi> ` ((\<Oplus> ( ((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| ((\<W> n (Suc k) \<R>) \<aa>\<^sub>1) ))))) \<inter> (\<Psi>\<^sub>\<phi> ` (\<Oplus> ( ((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>2) |`| ((\<W> n (Suc k) \<R>) \<aa>\<^sub>2)))))) 
                          \<subseteq> ((\<Psi>\<^sub>\<phi> ` (\<Uplus> ( ((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| ((\<W> n (Suc k) \<R>) \<aa>\<^sub>1) )))) \<inter> (\<Psi>\<^sub>\<phi> ` (\<Uplus> ( ((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>2) |`| ((\<W> n (Suc k) \<R>) \<aa>\<^sub>2))))))" by auto
        from q851 \<Z>\<^sub>\<phi>\<^sub>F_mono q1 \<Psi>\<^sub>\<Sigma>\<^sub>\<rho>_def dist_intersectionLanguageOplusRules_def paths_monoForest
        show "\<alpha> \<bullet>  (pifan\<union> {[]}) \<subseteq> \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F (Suc n) ((\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (((\<W> n (Suc k) \<R>) \<aa>\<^sub>1))((((\<W> n (Suc k) \<R>) \<aa>\<^sub>2))))))" by metis
      qed
      from q3 w_mono intersectMono z_mono paths_monoForest 
      have q4 : "\<alpha> \<bullet>  (pifan\<union> {[]}) \<subseteq> \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F (Suc n) ((\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (((\<R>) \<aa>\<^sub>1))((((\<R>) \<aa>\<^sub>2))))))"
      proof -
        from intersectMono w_mono 
        have q150 : "\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (((\<W> n (Suc k) \<R>) \<aa>\<^sub>1))((((\<W> n (Suc k) \<R>) \<aa>\<^sub>2))) \<subseteq> \<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (((\<R>) \<aa>\<^sub>1))((((\<R>) \<aa>\<^sub>2)))" by metis
        from q3 q150 paths_monoForest \<Z>\<^sub>\<phi>\<^sub>F_mono subset_trans        show "\<alpha> \<bullet> (pifan\<union> {[]}) \<subseteq> \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F (Suc n) ((\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (((\<R>) \<aa>\<^sub>1))((((\<R>) \<aa>\<^sub>2))))))"          by smt 
      qed
      from \<gg>_def pathsForestsTrees 
      have q5 : "(\<Pi>\<^sub>\<phi> (fset (\<Z>\<^sub>\<phi> (Suc n) ((\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (((\<R>) \<aa>\<^sub>1))((((\<R>) \<aa>\<^sub>2)))))))) = \<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> (Suc n) \<R>))" by metis
      from q4 q5 pifan_def \<Z>\<^sub>\<phi>\<^sub>F_def       have "\<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n (Suc k) \<R>))\<union> {[]}) \<subseteq> \<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> (Suc n) \<R>))"        by (simp add: \<Z>\<^sub>\<phi>\<Z>\<^sub>\<phi>\<^sub>Flemma) 
      then show "\<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n (Suc (Suc k)) \<R>))\<union> {[]}) \<subseteq> \<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> (Suc n) \<R>))" using f1HasNotChangedAnyMore by metis
      have b604 : "\<And> trel . trel \<in> (fset (\<ff> (Suc n)  \<R>)) \<Longrightarrow> root trel = \<alpha>"
      proof -
        fix trel
        assume q8124: "trel \<in> (fset (\<ff> (Suc n)  \<R>))"
        have h672 : "\<forall>\<ii>. satisfiesApproximatorForRuleSet trel (\<R> \<ii>) \<ii>"
        proof -
          from \<ff>_def have q8125 : "\<ff> (Suc n) \<R> = \<Z>\<^sub>\<tau> (Suc n) (\<P> \<R>)" by auto
          from q8124 q8125 have q8126 : "trel |\<in>| \<Z>\<^sub>\<tau> (Suc n) (\<P> \<R>)" by (simp add: fmember.rep_eq)
          from \<Z>\<tau>_subset \<Z>\<tau>_lemma Z_def q8126 notin_fset have 8127 : "trel \<in> \<P> \<R>" using subsetCE            by metis
          from \<P>_def 8127 show "\<forall>\<ii>. satisfiesApproximatorForRuleSet trel (\<R> \<ii>) \<ii>" by simp
        qed
        from theSingletonPathExists obtain path node where h673 : "path \<in> pathsInTree trel" and h674 : "path = [node]" and h675 : "down node = trel" by metis
        show "root trel = \<alpha>" proof -
          fix \<ii>
          from h672 h673 satisfiesApproximatorForRuleSet_def have h676 : "pathSatisfiesApproximatorForRuleSet path (\<R> \<ii>) \<ii>" by metis
          from h676 pathSatisfiesApproximatorForRuleSet_def obtain ruleSeq where t3285 : "hd ruleSeq |\<in>| (\<R> \<ii>) \<and> pathFitsListAndListIsARun \<ii> path ruleSeq" by auto
          from t3285 pathFitsListAndListIsARunImpliesV h674 have h679 : "(( (down (hd path))) \<in> ( \<V>\<^sub>\<tau> \<ii> (hd ruleSeq)  )   ) " by blast
          from h679 alphaIsTransition rootOfV t3285 have h680 : "root (down (hd path)) = \<alpha>" by metis
          from h674 have h681 : "hd path = node" by (simp add: list.sel(1)) 
          from h675 h680 h681 show "root trel = \<alpha>" by metis 
        qed
      qed
      show "\<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> (Suc n) \<R>)) \<subseteq> \<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n (Suc (Suc k)) \<R>))\<union> {[]})"
      proof -
        from \<gg>_def paths_monoTree gInF FSet.less_eq_fset.rep_eq 
        have q21 : "\<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> (Suc n) \<R>)) \<subseteq> \<Pi>\<^sub>\<tau>\<^sub>F ((((\<ff> (Suc n)  \<R>))))"
          by (simp add: less_eq_fset.rep_eq pathsTreeLangMonotone allRulesArePresent) 
        have q24 : "\<Pi>\<^sub>\<tau>\<^sub>F (((\<ff> (Suc n)  \<R>))) \<subseteq> \<alpha> \<bullet>  ((\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n (Suc k) \<R>)))\<union> {[]})"
        proof -
          from from_first have b600 :  "(\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) |\<subseteq>| (\<ff>\<^sub>1 n (Suc k) \<R>)" by auto
          from b600 
          have b601 : "\<Pi>\<^sub>\<tau>\<^sub>F ((\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>))) \<subseteq> (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n (Suc k) \<R>)))" by (simp add: less_eq_fset.rep_eq pathsTreeLangMonotone)
          then have "\<Pi>\<^sub>\<tau>\<^sub>F ((\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)))\<union> {[]} \<subseteq> (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n (Suc k) \<R>)))\<union> {[]}" by blast
          then
          have b602 : "\<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F ((\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)))\<union> {[]}) \<subseteq> \<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n (Suc k) \<R>))\<union> {[]})"  using prefixLetterMono by simp
          from  b604 factorAndPrefix         have "\<And>witness . witness \<in>( fset (((\<ff> (Suc n)  \<R>)))) \<Longrightarrow> \<alpha> \<bullet> \<Pi>\<^sub>\<tau> (\<alpha> \<diamondop>\<tau>\<lambda> (fset ((\<ff> (Suc n)  \<R>)))) \<union> {[\<alpha>]} = \<Pi>\<^sub>\<tau> (fset ((\<ff> (Suc n)  \<R>)))" by auto
          then have "\<alpha> \<bullet> \<Pi>\<^sub>\<tau> (\<alpha> \<diamondop>\<tau>\<lambda> (fset ((\<ff> (Suc n)  \<R>)))) \<union> {[\<alpha>]} = \<Pi>\<^sub>\<tau> (fset ((\<ff> (Suc n)  \<R>)))"                using fNotEmpty by auto
          then have  b603 : "\<alpha> \<bullet> (\<Pi>\<^sub>\<tau>  (\<alpha> \<diamondop>\<tau>\<lambda> (fset (\<ff> (Suc n)  \<R>)))\<union> {[]}) = \<Pi>\<^sub>\<tau>\<^sub>F (((\<ff> (Suc n)  \<R>)))" using unionAppend by auto
          from b603 factorByRootSymbolF_lemma b602 show "\<Pi>\<^sub>\<tau>\<^sub>F (((\<ff> (Suc n)  \<R>))) \<subseteq> \<alpha> \<bullet>  (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n (Suc k) \<R>))\<union> {[]})" by metis
        qed
        from q24 q21 f1HasNotChangedAnyMore show ?thesis by auto
      qed
    qed
  qed
    
    (* show that W becomes stationary because it is finite and monotone *)
  def tempw == "\<lambda> i. (\<lambda> k0 . \<W> n k0 \<R> i)"
  from finiteMonotoneStationary wMonotonic have h6577 : "\<And>i. ((\<And>n. tempw i (Suc n) |\<subseteq>| tempw i n) \<Longrightarrow> \<exists>k.(\<forall>k0. (k0 \<ge> k  \<longrightarrow> (tempw i k0)  = tempw i (Suc k0) )))" by blast
  from h6577 tempw_def wMonotonic tempw_def have h657876 : "\<And>i. (\<exists>k.(\<forall>k0. (k0 \<ge> k  \<longrightarrow> (tempw i k0)  = tempw i (Suc k0) )))" by blast
  then have "\<exists> k. \<forall> i. ((\<forall>k0. (k0 \<ge> k  \<longrightarrow> (tempw i k0)  = tempw i (Suc k0) )))"
  proof -
    from h657876 obtain k1 where k1a : "((\<forall>k0. (k0 \<ge> k1  \<longrightarrow> (tempw \<aa>\<^sub>1 k0)  = tempw \<aa>\<^sub>1 (Suc k0) )))" by blast
    from h657876 obtain k2 where k2a : "((\<forall>k0. (k0 \<ge> k2  \<longrightarrow> (tempw \<aa>\<^sub>2 k0)  = tempw \<aa>\<^sub>2 (Suc k0) )))" by blast    
    obtain kmax where k3a : "kmax > k1" and k3b : "kmax > k2"          using less_add_Suc1 less_add_Suc2 by blast 
    from k1a k3a have k4a : "((\<forall>k0. (k0 \<ge> kmax  \<longrightarrow> (tempw \<aa>\<^sub>1 k0)  = tempw \<aa>\<^sub>1 (Suc k0) )))"          by (meson less_le less_le_trans)
    from k2a k3b have k5a : "((\<forall>k0. (k0 \<ge> kmax  \<longrightarrow> (tempw \<aa>\<^sub>2 k0)  = tempw \<aa>\<^sub>2 (Suc k0) )))"  by (meson less_le less_le_trans)
    from k4a k5a have "\<forall> i. ((\<forall>k0. (k0 \<ge> kmax  \<longrightarrow> (tempw i k0)  = tempw i (Suc k0) )))"          by (metis \<A>.cases) 
    then show "\<exists> k. \<forall> i. ((\<forall>k0. (k0 \<ge> k  \<longrightarrow> (tempw i k0)  = tempw i (Suc k0) )))" by auto
  qed
  then have n764654 : "\<exists>k.(\<forall>k0. (k \<le> k0 \<longrightarrow> \<W> n (Suc k0) \<R> = \<W> n k0 \<R>))" using tempw_def by blast
      
      
  show "(\<exists>k. \<ff>\<^sub>1 n k \<R> = {||}) \<or> (\<exists>k. \<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>) \<union> {[]}) = \<Pi>\<^sub>\<tau>\<^sub>F (\<gg> (Suc n) \<R>))" using n764654 toShowMain firstGoal by blast
  show "\<And>k. \<alpha> \<diamondop> \<ff> (Suc n) \<R> |\<subseteq>| \<ff>\<^sub>1 n k \<R> " using n764654 toShowMain firstGoal by blast
qed
  
  
  
  
  
  
  
lemma core_main_lemma2 :
  fixes l
  fixes \<R>
  fixes n
  fixes j                   
  fixes \<alpha> 
    assumes allRulesArePresent : "(\<And>i rule. rule |\<in>| rule_set (\<A> i))"
  assumes "\<And> r i. r |\<in>| \<R> i \<Longrightarrow> (r |\<in>| rule_set (\<A> i) \<and> symbol r = \<alpha>)"
    
  assumes statesLanguagesNonempty : "\<And> \<ii> r. r |\<in>| (\<R> \<ii>) \<Longrightarrow>   (\<And> s . s |\<in>| (states r) \<Longrightarrow> ((\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>) s)  \<noteq> {}))"
  assumes alphaIsTransition : "\<And> \<ii> rule . rule |\<in>| (\<R> \<ii>) \<Longrightarrow> symbol rule = \<alpha>"
  assumes fNotEmpty : "fset (\<ff> (Suc n)  \<R>) \<noteq> {}"
    
  assumes outerHypothesis : "\<And> rs2. (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> n  rs2))) = \<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> n rs2))"
  assumes inStateSet : "\<And> \<ii>. \<And> r . \<And> s . r |\<in>| (\<R> \<ii>) \<Longrightarrow> s |\<in>| states r \<Longrightarrow> s |\<in>| state_set (\<A> \<ii>)"
  assumes nAssum : "Suc n > \<N>"
  assumes    rulesLangsNonempty : "\<And> \<R> i r . (r |\<in>| rule_set (\<A> i) \<Longrightarrow>  ((\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) r)  \<noteq> {}))"
  shows "(\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n)  \<R>))) = \<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> (Suc n) \<R>))"
proof (rule disjE)
  have a2 : "\<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> (Suc n) \<R>)) \<subseteq> \<Pi>\<^sub>\<tau>\<^sub>F (\<ff> (Suc n)  \<R>)"    by (metis assms \<gg>_def gInF less_eq_fset.rep_eq pathsTreeLangMonotone)
  have b689 : "(\<And>tr. tr |\<in>| (\<ff> (Suc n) \<R>) \<Longrightarrow> root tr = \<alpha>)"    using alphaIsTransition fRoot by meson
  from factorAndPrefix fNotEmpty have m70 : "\<And>witness. (\<And>tr. tr \<in> (fset (\<ff> (Suc n)  \<R>)) \<Longrightarrow> root tr = \<alpha>) \<Longrightarrow>  \<alpha> \<bullet> \<Pi>\<^sub>\<tau> (\<alpha> \<diamondop>\<tau>\<lambda> (fset (\<ff> (Suc n)  \<R>))) \<union> {[\<alpha>]} = \<Pi>\<^sub>\<tau> (fset (\<ff> (Suc n)  \<R>))" by blast
        from  factorAndPrefix b689 factorByRootSymbolF_lemma(2) less_eq_fset.rep_eq notin_fset pathsTreeLangMonotone prefixLetterMono   have m71 : "(\<And>tr. tr \<in> (fset (\<ff> (Suc n)  \<R>)) \<Longrightarrow> root tr = \<alpha>)"     by fastforce
  from m70 m71 have m72 : "\<alpha> \<bullet> \<Pi>\<^sub>\<tau> (\<alpha> \<diamondop>\<tau>\<lambda> (fset (\<ff> (Suc n)  \<R>))) \<union> {[\<alpha>]} = \<Pi>\<^sub>\<tau> (fset (\<ff> (Suc n)  \<R>))" by auto
      
  from core_main_lemma show "(\<exists>k. \<ff>\<^sub>1 n k \<R> = {||}) \<or> (\<exists>k . ( \<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))\<union> {[]}) =  \<Pi>\<^sub>\<tau>\<^sub>F ((  \<gg> (Suc n) \<R>))))" using assms by auto
  from core_main_lemma have secondPart : "\<And> k . (\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) |\<subseteq>| \<ff>\<^sub>1 n k \<R>" using assms by auto
      
  {
    assume n764654 : "(\<exists>k. \<ff>\<^sub>1 n k \<R> = {||})"
    hence n764654 : "(\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) = {||}"  using secondPart by blast
    from fNotEmpty have "(\<ff> (Suc n)  \<R>) \<noteq> fempty" by auto
    then obtain tree where n76465 : "tree |\<in>| (\<ff> (Suc n)  \<R>)" and n65786 : "root tree = \<alpha>" using b689          by auto 
    from b689 have "\<alpha> \<bullet> \<Pi>\<^sub>\<tau> (\<alpha> \<diamondop>\<tau>\<lambda> (fset (\<ff> (Suc n)  \<R>))) \<union> {[\<alpha>]} = \<Pi>\<^sub>\<tau> (fset (\<ff> (Suc n)  \<R>))" using m70 notin_fset by metis
        
    from n764654 have "(\<alpha> \<diamondop>\<tau>\<lambda> (fset (\<ff> (Suc n)  \<R>))) = {}" using factorByRootSymbolF_lemma by blast
    hence "\<alpha> \<bullet> \<Pi>\<^sub>\<tau> (\<alpha> \<diamondop>\<tau>\<lambda> (fset (\<ff> (Suc n)  \<R>))) = {}" using prefixLetter_def pathsForTreeLanguage_def
    proof -
      show ?thesis
        by (simp add: \<open>\<alpha> \<diamondop>\<tau>\<lambda> fset (\<ff> (Suc n) \<R>) = {}\<close> pathsForTreeLanguage_def prefixLetter_def)
    qed
    hence n764654 : "\<Pi>\<^sub>\<tau> (fset (\<ff> (Suc n)  \<R>)) = {[\<alpha>]}" using m72 by auto
    hence n656897 : "\<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> (Suc n) \<R>)) \<subseteq>  {[\<alpha>]}" using a2 by blast
        
        
    from n764654 have n75478 : "\<And>tree path . tree \<in> (fset (\<ff> (Suc n)  \<R>)) \<Longrightarrow> (path |\<in>| (\<Pi> tree)) \<Longrightarrow> path = [\<alpha>]" using pathsForTreeLanguage_def by blast
    hence "\<And>tree path . tree \<in> (fset (\<ff> (Suc n)  \<R>)) \<Longrightarrow> (path |\<in>| (\<Pi> tree)) \<Longrightarrow> length path = length [\<alpha>] " by auto
    hence "\<And>tree path . tree \<in> (fset (\<ff> (Suc n)  \<R>)) \<Longrightarrow> (path |\<in>| (\<Pi> tree)) \<Longrightarrow> length path = 1 " by auto
    hence "\<And>tree path . tree \<in> (fset (\<ff> (Suc n)  \<R>)) \<Longrightarrow> (path |\<in>| (\<Pi> tree)) \<Longrightarrow> length path \<le> 1 " by auto
    hence "\<And>tree .  tree \<in> (fset (\<ff> (Suc n)  \<R>)) \<Longrightarrow> height tree \<le> 1" using heightOnlyDependsOnPaths finiteMaxExists  by (metis One_nat_def fimageE le_SucI le_zero_eq) 
    hence n7656897 :  "\<And>tree .  tree \<in> (fset (\<Z>\<^sub>\<tau> (Suc n)(\<P> \<R>))) \<Longrightarrow> height tree \<le> 1"  using \<ff>_def by auto
    hence "\<And>tree .  tree \<in> (fset (\<Z>\<^sub>\<tau> (Suc n)(\<P> \<R>))) \<Longrightarrow> tree \<in> (\<P> \<R>)" using \<Z>\<^sub>\<tau>_def notin_fset    by (metis \<ff>_def zInP)
    hence "\<And>tree i .  tree \<in> (fset (\<Z>\<^sub>\<tau> (Suc n)(\<P> \<R>))) \<Longrightarrow> tree \<in> (\<P>\<^sub>1 \<R> i)" using \<P>_def \<P>\<^sub>1_def by auto
    hence n6587 : "\<And>tree i .  tree \<in> (fset (\<Z>\<^sub>\<tau> (Suc n)(\<P> \<R>))) \<Longrightarrow> tree |\<in>| \<Z>\<^sub>\<tau> 1 (\<P>\<^sub>1 \<R> i)" using \<Z>\<^sub>\<tau>_def  n7656897          by (simp add: finterI restrictionIsFinite2) 
        
    have n76875654 : "tree \<in> (fset (\<ff> (Suc n)  \<R>))" using n76465 notin_fset by metis
    from n65786 tree.exhaust root.simps obtain children where n7565687 : "tree = (NODE \<alpha> children)"      by metis 
    from n7565687 rootIsPath  have n65687 : "[\<alpha>] |\<in>| \<delta>\<^sub>\<tau> tree" by auto
    from n75478 n65687 n76875654 have n65t687543 : "\<delta>\<^sub>\<tau> tree = (finsert [\<alpha>] fempty)"          by blast  
    have n76867 : " tree \<in> (fset (\<Z>\<^sub>\<tau> (Suc n)(\<P> \<R>)))" using n76465 \<ff>_def notin_fset by metis
    have n678y77 : "\<And>path . path |\<in>|  (finsert [\<alpha>] fempty)  \<Longrightarrow> length path \<le> 1 "        by simp 
    hence n678y77b : "\<And>path . path |\<in>|  (finsert [\<alpha>] fempty)  \<Longrightarrow> length path \<le> (Suc n) "              by simp 
        
    have n657988 : "1 \<le> \<N>" using existsUniformConstant assms by auto
    from smallerThanN n657988 have "\<And> f \<ii> \<R> .  f |\<in>| \<Z>\<^sub>\<tau> 1 (\<P>\<^sub>1 \<R> \<ii>) \<Longrightarrow> \<delta>\<^sub>\<tau> f \<in> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>) |`| \<R> \<ii>)" by auto
    hence "\<And>tree i . tree \<in> (fset (\<Z>\<^sub>\<tau> (Suc n)(\<P> \<R>))) \<Longrightarrow> \<delta>\<^sub>\<tau> tree \<in> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i)" using n6587 by auto
    hence "\<And> i . \<delta>\<^sub>\<tau> tree \<in> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i)" using n76867 by auto       
    hence "\<And> i . (\<exists> z . (z \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i)) \<and> \<delta>\<^sub>\<tau> tree = \<Pi>\<^sub>\<iota>\<^sub>\<phi> z)" using n76867          using n65687 by fastforce 
    hence "\<And> i . (\<exists> z . (z \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i)) \<and> (finsert [\<alpha>] fempty) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> z)" using n65t687543 by auto
    hence "\<And> i . (\<exists> z . (z \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i)) \<and> (finsert [\<alpha>] fempty) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> z \<and> (\<forall> path. path |\<in>|  \<Pi>\<^sub>\<iota>\<^sub>\<phi> z \<longrightarrow> length path \<le>(Suc n)))" using n678y77b by metis
    hence "\<And> i . (\<exists> z . (\<Psi>\<^sub>\<phi> z \<in> \<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i)) \<and> (finsert [\<alpha>] fempty) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> z \<and> (\<forall> path. path |\<in>|  \<Pi>\<^sub>\<iota>\<^sub>\<phi> z \<longrightarrow> length path \<le>(Suc n)))"    by blast
    hence "\<And> i . (\<exists> z . (\<Psi>\<^sub>\<phi> z \<in> \<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i)) \<and> (finsert [\<alpha>] fempty) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> z) \<and> (\<forall> path. path |\<in>|  \<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> z) \<longrightarrow> length path \<le>(Suc n)))"    using psiPreservesPaths by auto
    hence n7y5e3543 : "\<And> i . (\<exists> z . (z \<in> \<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i)) \<and> (finsert [\<alpha>] fempty) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> (z) \<and> (\<forall> path. path |\<in>|  \<Pi>\<^sub>\<iota>\<^sub>\<phi> (z) \<longrightarrow> length path \<le>(Suc n)))"  by blast
        
    def z0 == "\<Psi>\<^sub>\<phi> (finsert tree fempty)" 
    hence "\<Pi>\<^sub>\<iota>\<^sub>\<phi> z0 = \<delta>\<^sub>\<tau> tree"        by (simp add: pathsSingeton psiPreservesPaths) 
    hence n8u6354 : "\<Pi>\<^sub>\<iota>\<^sub>\<phi> z0 = (finsert [\<alpha>] fempty)"   using n65t687543 by auto
        
    hence "\<And> i . (\<exists> z . (z \<in> \<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i)) \<and> (finsert [\<alpha>] fempty) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> (z) \<and> z = z0 \<and> (\<forall> path. path |\<in>|  \<Pi>\<^sub>\<iota>\<^sub>\<phi> (z) \<longrightarrow> length path \<le>(Suc n)))"       using n7y5e3543 psiOnlyDependsOnPath      by (metis image_iff psiPreservesPaths z0_def) 
        
    hence n754654 : "\<And> i . ((z0 \<in> \<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) |`| \<R> i)) \<and> (finsert [\<alpha>] fempty) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> (z0) \<and> (\<forall> path. path |\<in>|  \<Pi>\<^sub>\<iota>\<^sub>\<phi> (z0) \<longrightarrow> length path \<le>(Suc n)))"   by blast
    hence n867454 : "z0 \<in> \<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2)" using \<Psi>\<^sub>\<Sigma>\<^sub>\<rho>_def          by (metis Int_iff aut_def) 
    from n754654  have   "(\<And> path. path |\<in>|  \<Pi>\<^sub>\<iota>\<^sub>\<phi> (z0) \<Longrightarrow> length path \<le>(Suc n))" by auto
    hence   "(\<And> tree. tree |\<in>|   (z0) \<Longrightarrow> height tree \<le>(Suc n))" using heightOnlyDependsOnPaths finiteMaxExists  by (metis (no_types, lifting) fimageE less_Suc_eq_le pathsTreeForest zero_less_Suc) 
    hence n5487 : " (z0)  \<in> {f. \<forall>t. t |\<in>| f \<longrightarrow> height t \<le> (Suc n)}" by auto 
    from n867454 n5487 \<Z>\<^sub>\<phi>_def have n754543 : "z0 |\<in>| (\<Z>\<^sub>\<phi> (Suc n) (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2)))"      by (smt Collect_cong finterI notin_fset restrictionIsFiniteForests)  
        
    have n65354 : "[\<alpha>] |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> z0" using n8u6354 by auto
        
    have "[\<alpha>] \<in> \<Pi>\<^sub>\<tau>\<^sub>F (\<Union>| (\<Z>\<^sub>\<phi> (Suc n) (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))))" using n754543 n65354 pathsForTreeLanguage_def ffUnionLemma notin_fset        by (smt pathsTreeForest piFset) 
    hence    "\<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> (Suc n) \<R>)) =  {[\<alpha>]}" using n656897 \<gg>_def by auto
    then show "(\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n)  \<R>))) = \<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> (Suc n) \<R>))" using n764654 by auto
        
      
      }
      
  {
    assume "(\<exists>k . ( \<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))\<union> {[]}) =  \<Pi>\<^sub>\<tau>\<^sub>F ((  \<gg> (Suc n) \<R>))))"
    then obtain k where a1 : "( \<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>))\<union> {[]}) =  \<Pi>\<^sub>\<tau>\<^sub>F ((  \<gg> (Suc n) \<R>)) \<and> (\<alpha> \<diamondop> (\<ff> (Suc n)  \<R>)) |\<subseteq>| \<ff>\<^sub>1 n k \<R>)" using secondPart by auto
        
    from a1 have "\<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>) \<union> {[]}) = \<Pi>\<^sub>\<tau>\<^sub>F (\<gg> (Suc n) \<R>)" by auto
    from a1 have a1b : "\<alpha> \<diamondop> \<ff> (Suc n) \<R> |\<subseteq>| \<ff>\<^sub>1 n k \<R>" by auto
    from m72 a1b factorByRootSymbolF_lemma have "\<Pi>\<^sub>\<tau>\<^sub>F (\<ff> (Suc n)  \<R>) \<subseteq> \<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>)) \<union> {[\<alpha>]}" by  (metis Un_mono Un_upper1 insert_is_Un less_eq_fset.rep_eq pathsTreeLangMonotone prefixLetterMono) 
    then have "\<Pi>\<^sub>\<tau>\<^sub>F (\<ff> (Suc n)  \<R>) \<subseteq> \<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<ff>\<^sub>1 n k \<R>) \<union> {[]})" using unionAppend by auto
    then have  a3 : "\<Pi>\<^sub>\<tau>\<^sub>F (\<ff> (Suc n)  \<R>) \<subseteq> ( \<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff>\<^sub>1 n k \<R>)) \<union> {[]}))"  by auto
    show "(\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n)  \<R>))) = \<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> (Suc n) \<R>))" using a1 a2 a3    by auto 
  }
qed
  
  
  
  
  
  
lemma core_main_lemma4 :
  fixes l
  fixes \<R>
  fixes n
  fixes j
    assumes allRulesArePresent : "(\<And>i rule. rule |\<in>| rule_set (\<A> i))"
  assumes "\<And> r i. r |\<in>| \<R> i \<Longrightarrow> (r |\<in>| rule_set (\<A> i))"
    
  assumes statesLanguagesNonempty : "\<And> \<ii> r. r |\<in>| (\<R> \<ii>) \<Longrightarrow>   (\<And> s . s |\<in>| (states r) \<Longrightarrow> ((\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>) s)  \<noteq> {}))"
  assumes fNotEmpty : "fset (\<ff> (Suc n)  \<R>) \<noteq> {}"
    
  assumes outerHypothesis : "\<And> rs2. (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> n  rs2))) = \<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> n rs2))"
  assumes inStateSet : "\<And> \<ii>. \<And> r . \<And> s . r |\<in>| (\<R> \<ii>) \<Longrightarrow> s |\<in>| states r \<Longrightarrow> s |\<in>| state_set (\<A> \<ii>)"
  assumes nAssum : "Suc n > \<N>"
  assumes    rulesLangsNonempty : "\<And> \<R> i r . (r |\<in>| rule_set (\<A> i) \<Longrightarrow>  ((\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) r)  \<noteq> {}))"
  shows "(\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n)  \<R>))) = \<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> (Suc n) \<R>))"
proof -
  def rulesPerAlpha == "(\<lambda> \<alpha>. (\<lambda>\<ii>. (ffilter (\<lambda>rule. symbol rule = \<alpha>) (\<R> \<ii>))))"
  from rulesPerAlpha_def have b1 : "\<And> \<alpha> \<ii>.(rulesPerAlpha \<alpha> \<ii> |\<subseteq>| (\<R> \<ii>))" using ffmember_filter fsubsetI by fastforce
  from b1 statesLanguagesNonempty have alpha_statesLanguagesNonempty : "\<And> \<alpha> \<ii> r. r |\<in>| (rulesPerAlpha \<alpha> \<ii>) \<Longrightarrow>   (\<And> s . s |\<in>| (states r) \<Longrightarrow> ((\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>) s)  \<noteq> {}))" by blast
  from b1 inStateSet have alpha_inStateSet : "\<And> \<ii> \<alpha>. \<And> r . \<And> s . r |\<in>| (rulesPerAlpha \<alpha> \<ii>) \<Longrightarrow> s |\<in>| states r \<Longrightarrow> s |\<in>| state_set (\<A> \<ii>)" by blast
  def occurringAlphas == "ffilter (\<lambda> \<alpha> . fset (\<ff> (Suc n)  (rulesPerAlpha \<alpha>)) \<noteq> {}) (fimage symbol (\<R> \<aa>\<^sub>1) |\<union>| fimage symbol (\<R> \<aa>\<^sub>2))"
  from occurringAlphas_def have alpha_fNotEmpty : "\<forall> \<alpha> . \<alpha> |\<in>| occurringAlphas \<longrightarrow> fset (\<ff> (Suc n)  (rulesPerAlpha \<alpha>)) \<noteq> {}" by (simp add: ffmember_filter)
  def gAlpha == "\<lambda> \<alpha> . (((\<gg> (Suc n) (rulesPerAlpha \<alpha>))))"
    
    (* apply main lemma for each \<alpha> individually *)
  have u1 : "\<And> \<alpha> . \<alpha> |\<in>| occurringAlphas \<Longrightarrow> (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n)  (rulesPerAlpha \<alpha>)))) = \<Pi>\<^sub>\<tau>\<^sub>F ((gAlpha \<alpha>))"
  proof -
    fix \<alpha>
    assume "\<alpha> |\<in>| occurringAlphas"
    define Ra where z1 : "Ra = (rulesPerAlpha \<alpha>)"
    from rulesPerAlpha_def z1 have z2 : "\<And>i r . r |\<in>| Ra i \<Longrightarrow> symbol r = \<alpha> \<and> r |\<in>| \<R> i" by simp
    from z1 z2 have rulesInAA : "\<And> r i. r |\<in>| Ra i \<Longrightarrow> (r |\<in>| rule_set (\<A> i) \<and> symbol r = \<alpha>)"  using assms(1) by auto
    have statesLanguagesNonemptyA : "\<And> \<ii> r. r |\<in>| (Ra \<ii>) \<Longrightarrow>   (\<And> s . s |\<in>| (states r) \<Longrightarrow> ((\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>) s)  \<noteq> {}))" using assms z2  by blast
    have alphaIsTransitionA : "\<And> \<ii> rule . rule |\<in>| (Ra \<ii>) \<Longrightarrow> symbol rule = \<alpha>" using assms z2  by simp
    have fNotEmptyA : "fset (\<ff> (Suc n)  Ra) \<noteq> {}" using assms z2  by (simp add: \<open>\<alpha> |\<in>| occurringAlphas\<close> alpha_fNotEmpty z1)
    have outerHypothesisA : "\<And> rs2. (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> n  rs2))) = \<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> n rs2))" using assms z2 by auto
    have inStateSetA : "\<And> \<ii>. \<And> r . \<And> s . r |\<in>| (Ra \<ii>) \<Longrightarrow> s |\<in>| states r \<Longrightarrow> s |\<in>| state_set (\<A> \<ii>)" using assms z2 by blast
    from core_main_lemma2 show " \<Pi>\<^sub>\<tau>\<^sub>F (\<ff> (Suc n) (rulesPerAlpha \<alpha>)) = \<Pi>\<^sub>\<tau>\<^sub>F (gAlpha \<alpha>)"    
      using fNotEmptyA gAlpha_def inStateSetA nAssum  outerHypothesisA rulesInAA statesLanguagesNonemptyA z1 rulesLangsNonempty allRulesArePresent by auto
  qed
    
  have u2 : "(\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n)  \<R>))) = Union (image (\<lambda> \<alpha> . (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n)  (rulesPerAlpha \<alpha>))))) (fset occurringAlphas))"
  proof
    show "\<Union>((\<lambda>\<alpha>. \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n) (rulesPerAlpha \<alpha>)))) ` fset occurringAlphas) \<subseteq> \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n) \<R>))"
    proof
      fix x
      assume y1 : "x \<in> \<Union>((\<lambda>\<alpha>. \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n) (rulesPerAlpha \<alpha>)))) ` fset occurringAlphas)"
      from y1 obtain \<alpha> where y2 : "\<alpha> \<in> (fset occurringAlphas)" and y3 : "x \<in> \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n) (rulesPerAlpha \<alpha>)))" by blast
      have "\<And>i . (rulesPerAlpha \<alpha> i) |\<subseteq>| \<R> i"        by (simp add: b1)
      then have "\<P> (rulesPerAlpha \<alpha>) \<subseteq> \<P> \<R>" using \<P>_def satisfiesApproximatorForRuleSet_def pathSatisfiesApproximatorForRuleSet_def            by fastforce    
      then have y4 : "(\<ff> (Suc n) (rulesPerAlpha \<alpha>)) |\<subseteq>| (\<ff> (Suc n)  \<R>)" using \<ff>_def   by (metis fsubsetI subsetCE zIntersectLemma) 
      from y3 y4 show "x \<in> \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n) \<R>))" by (simp add: less_eq_fset.rep_eq pathsTreeLangMonotone rev_subsetD)
    qed
    show "\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n) \<R>)) \<subseteq> \<Union>((\<lambda>\<alpha>. \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n) (rulesPerAlpha \<alpha>)))) ` fset occurringAlphas)"
    proof 
      fix p
      assume "p \<in> \<Pi>\<^sub>\<tau>\<^sub>F (\<ff> (Suc n) \<R>)"
      then obtain tr where w1 : "p |\<in>| \<Pi> tr" and w2 : "height tr \<le> (Suc n)" and w3 : "tr \<in> \<P> \<R>" using pathsForTreeLanguage_def \<ff>_def zIntersectLemma        by (smt Z_def \<Z>\<tau>_lemma mem_Collect_eq) 
      then have w4 : "\<And>\<ii>.(\<forall> p \<in> (pathsInTree tr) .           (\<exists> r  . (hd r |\<in>| (\<R> \<ii>)) \<and>                      (pathFitsListAndListIsARun \<ii> p r)))" using \<P>_def w3 satisfiesApproximatorForRuleSet_def pathSatisfiesApproximatorForRuleSet_def by auto
      def \<alpha> == "root tr"
      have k76y78 : "((\<And> \<ii>.(\<And> p . p \<in> (pathsInTree tr) \<Longrightarrow>    (\<exists> r  . (hd r |\<in>| ((rulesPerAlpha \<alpha>) \<ii>)) \<and> (pathFitsListAndListIsARun \<ii> p r)))))"
      proof -
        fix \<ii> p
        assume f1 : "p \<in> (pathsInTree tr)"
        from w4 f1 obtain r where "(hd r |\<in>| (\<R> \<ii>)) \<and> (pathFitsListAndListIsARun \<ii> p r)" by blast
        then have w5 : "p = (hd p)#(tl p) \<Longrightarrow> (( (labelOfNode (hd p) = symbol (hd r))                                      \<and> ( (hd r) |\<in>| rule_set (\<A> \<ii>))))" using pathFitsListAndListIsARun.simps                by (metis hd_Cons_tl)
        then have w6 : "\<alpha> = (labelOfNode (hd p))"
        proof -
          have "isAPathp p \<and> (\<exists>n ns. p = n # ns \<and> down n = tr)"
            using f1 pathsInTree_def by auto
          then show ?thesis
            by (metis (no_types) \<alpha>_def labelOfNode_def list.sel(1))
        qed
        have "symbol (hd r) = \<alpha>"                    by (metis f1 hd_Cons_tl noEmptyPathsInTree w5 w6)
        then have "hd r |\<in>| ((rulesPerAlpha \<alpha>) \<ii>)"                    by (simp add: \<open>hd r |\<in>| \<R> \<ii> \<and> pathFitsListAndListIsARun \<ii> p r\<close> rulesPerAlpha_def)
        then show "(\<exists> r  . (hd r |\<in>| ((rulesPerAlpha \<alpha>) \<ii>)) \<and> (pathFitsListAndListIsARun \<ii> p r))"                    using \<open>hd r |\<in>| \<R> \<ii> \<and> pathFitsListAndListIsARun \<ii> p r\<close> by auto    
      qed
      from k76y78 have n76 : "tr \<in> \<P> (rulesPerAlpha \<alpha>)" using \<P>_def satisfiesApproximatorForRuleSet_def pathSatisfiesApproximatorForRuleSet_def by auto
      then have "tr |\<in>| (\<ff> (Suc n) (rulesPerAlpha \<alpha>))" using w2 \<ff>_def        by (simp add: Z_def \<Z>\<tau>_lemma fmember.rep_eq) 
      then have n476 : "p \<in> \<Pi>\<^sub>\<tau>\<^sub>F (\<ff> (Suc n) (rulesPerAlpha \<alpha>))" using w1 pathsForTreeLanguage_def      by (metis (mono_tags, lifting) mem_Collect_eq notin_fset)   
      from pRoot have j677 : "\<And> \<ii> r. (r |\<in>|  (rulesPerAlpha \<alpha>) \<ii> \<Longrightarrow> symbol r = \<alpha>) \<Longrightarrow> root tr = \<alpha>" using n76        by (simp add: \<alpha>_def)
      have "\<exists> p .  p \<in> (pathsInTree tr)"        using nodeListFitsTree w1 by auto 
      then have "\<And> \<ii>.  (\<exists> r. (r |\<in>|  (rulesPerAlpha \<alpha>) \<ii>))" using k76y78 by blast
      then have j54t68 : "\<And> \<ii>.  (\<exists> r. (r |\<in>|  (rulesPerAlpha \<alpha>) \<ii> \<and> symbol r = \<alpha>))" using rulesPerAlpha_def by auto
      from j54t68 rulesPerAlpha_def  \<alpha>_def n76 have "\<And> \<ii> . (\<exists> r. (r |\<in>| (rulesPerAlpha \<alpha>) \<ii> \<and> symbol r = \<alpha>)  \<and> root tr = \<alpha>)"           by blast         
      then have "\<And> \<ii> . (\<exists> r. (r |\<in>| (\<R>) \<ii>   \<and> root tr = symbol r))"              using b1 by blast 
      then have q76 : "root tr |\<in>| (fimage symbol (\<R> \<aa>\<^sub>1) |\<union>| fimage symbol (\<R> \<aa>\<^sub>2))"       by fastforce 
      from n76 \<alpha>_def have q77 : "fset (\<ff> (Suc n) (rulesPerAlpha (root tr))) \<noteq> {}"      by (metis \<open>tr |\<in>| \<ff> (Suc n) (rulesPerAlpha \<alpha>)\<close> bot_fset.rep_eq fempty_iff notin_fset) 
      from q76 q77 have e1 : "\<alpha> |\<in>| occurringAlphas" using occurringAlphas_def      by (simp add: \<alpha>_def) 
      then show "p \<in> \<Union>((\<lambda>\<alpha>. \<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n) (rulesPerAlpha \<alpha>)))) ` fset occurringAlphas)" using e1   n476       by (meson UN_iff fmember.rep_eq) 
    qed
  qed
    
  have u3 : "\<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> (Suc n) \<R>)) =  Union (image (\<lambda> \<alpha> .  ( \<Pi>\<^sub>\<tau>\<^sub>F ((gAlpha \<alpha>))))  (fset occurringAlphas)   )"
  proof
    show "\<Union>((\<lambda>\<alpha>. \<Pi>\<^sub>\<tau>\<^sub>F ((gAlpha \<alpha>))) ` fset occurringAlphas) \<subseteq> \<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> (Suc n) \<R>))"
    proof
      fix x
      assume y1 : "x \<in> \<Union>((\<lambda>\<alpha>. \<Pi>\<^sub>\<tau>\<^sub>F ((gAlpha \<alpha>))) ` fset occurringAlphas)"
      from y1 obtain \<alpha> where y2 : "\<alpha> \<in> (fset occurringAlphas)" and y3 : "x \<in> \<Pi>\<^sub>\<tau>\<^sub>F ((gAlpha \<alpha>))" by blast
      from b1 intersectMono gAlpha_def \<gg>_def have y4 : "(gAlpha \<alpha>) |\<subseteq>| (\<gg> (Suc n) \<R>)" by (simp add: \<Z>\<^sub>\<phi>_mono)
      from y3 y4 show "x \<in> \<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> (Suc n) \<R>))" by (simp add: less_eq_fset.rep_eq pathsTreeLangMonotone rev_subsetD)
    qed
    show "\<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> (Suc n) \<R>)) \<subseteq> \<Union>((\<lambda>\<alpha>. \<Pi>\<^sub>\<tau>\<^sub>F ((gAlpha \<alpha>))) ` fset occurringAlphas)"
    proof -
      have n767988 : "((\<gg> (Suc n) \<R>)) |\<subseteq>| \<Union>|((\<lambda>\<alpha>. ((gAlpha \<alpha>))) |`|  occurringAlphas)"
      proof 
        fix x
        assume n675987 : " x |\<in>| \<gg> (Suc n) \<R>"
        then have "x |\<in>| \<Union>| (\<Z>\<^sub>\<phi> (Suc n) (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (((\<R>) \<aa>\<^sub>1))((((\<R>) \<aa>\<^sub>2)))))" using \<gg>_def by auto
        then obtain y where q1 : "x |\<in>| y" and q2 : "y |\<in>| (\<Z>\<^sub>\<phi> (Suc n) (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (((\<R>) \<aa>\<^sub>1))((((\<R>) \<aa>\<^sub>2)))))"  by auto 
        then have "height x \<le> Suc n" using q1 q2
        proof -
          have "x \<in> Z (Suc n) (\<P> \<R>)"            by (metis (no_types) assms \<Z>\<tau>_lemma \<ff>_def \<open>x |\<in>| \<Union>| (\<Z>\<^sub>\<phi> (Suc n) (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2)))\<close> fmember.rep_eq gInF less_eq_fset.rep_eq subsetCE)
          then show ?thesis            using Z_def by blast
        qed 
        from q2 have n766 : "y \<in> (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (((\<R>) \<aa>\<^sub>1))((((\<R>) \<aa>\<^sub>2))))"
        proof -
          have "\<forall>f F Fa. (f::abc tree fset) \<notin> F \<inter> Fa \<or> f \<in> Fa"            by (metis IntD2)
          then show ?thesis            by (metis (no_types) \<Z>\<^sub>\<phi>_def fmember.rep_eq inf_fset2.rep_eq q2)
        qed 
        def \<alpha> == "root x"
          
        have n64r57689 :  "\<alpha> |\<in>| occurringAlphas"
        proof -
          from \<alpha>_def have n766897 : "\<alpha> = root x" by auto
          from occurringAlphas_def have "occurringAlphas = ( ffilter (\<lambda> \<alpha> . fset (\<ff> (Suc n)  (rulesPerAlpha \<alpha>)) \<noteq> {}) (fimage symbol (\<R> \<aa>\<^sub>1) |\<union>| fimage symbol (\<R> \<aa>\<^sub>2)))" by auto
          from n675987 have " x |\<in>| \<gg> (Suc n) \<R>" by auto
          then have n754654 : " x |\<in>| \<ff> (Suc n) \<R>" by (meson assms \<open>x |\<in>| \<Union>| (\<Z>\<^sub>\<phi> (Suc n) (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2)))\<close> fset_rev_mp gInF)
          from u2 have "(\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n)  \<R>))) = Union (image (\<lambda> \<alpha> . (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n)  (rulesPerAlpha \<alpha>))))) (fset occurringAlphas))" by auto
          from n766897 have "[\<alpha>] |\<in>| \<Pi> x"     by (metis root.simps rootIsPath tree.exhaust) 
          hence n645787 : "root x = \<alpha>"                by (simp add: n766897) 
          from n754654 \<ff>_def \<Z>\<^sub>\<tau>_def have n6756988 : "x \<in> \<P> \<R>"                by (simp add: zInP)
          have n6545877 : "x \<in> \<P> (rulesPerAlpha \<alpha>) \<and> (\<forall> \<ii> . \<alpha> |\<in>| fimage symbol (\<R> \<ii>))"
          proof -
            from n6756988 have n6576 : " \<And> \<ii>. satisfiesApproximatorForRuleSet x (\<R> \<ii>) \<ii>" using \<P>_def by auto
            from satisfiesApproximatorForRuleSet_def n6576 have n6478 : "\<And>\<ii> p . p\<in>pathsInTree x \<Longrightarrow> pathSatisfiesApproximatorForRuleSet p (\<R> \<ii>) \<ii>" by auto
            from pathSatisfiesApproximatorForRuleSet_def n6478 have  "\<And>\<ii> p . p\<in>pathsInTree x \<Longrightarrow> (\<exists> r.  hd r |\<in>| (\<R> \<ii>) \<and> pathFitsListAndListIsARun \<ii> p r)" by auto
            hence "\<And>\<ii> p . p\<in>pathsInTree x \<Longrightarrow> (\<exists> r.  hd r |\<in>| (\<R> \<ii>) \<and> pathFitsListAndListIsARun \<ii> p r)" by auto
            hence "\<And>\<ii> p . p\<in>pathsInTree x \<Longrightarrow> (\<exists> r.  (p \<noteq> []) \<and> hd r |\<in>| (\<R> \<ii>) \<and> pathFitsListAndListIsARun \<ii> p r)"  using pathsInTree_def by auto
            hence "\<And>\<ii> p . p\<in>pathsInTree x \<Longrightarrow> (\<exists> r phead ptail.  (p = phead#ptail) \<and> hd r |\<in>| (\<R> \<ii>) \<and> pathFitsListAndListIsARun \<ii> p r)"  using list.exhaust by metis
            hence "\<And>\<ii> p . p\<in>pathsInTree x \<Longrightarrow> (\<exists> r phead ptail rhead rtail. (r = rhead#rtail) \<and> (p = phead#ptail) \<and> hd r |\<in>| (\<R> \<ii>) \<and> pathFitsListAndListIsARun \<ii> p r)" 
              using pathFitsListAndListIsARun.cases                by (metis hd_Cons_tl pathFitsListAndListIsARun.simps(3))  
            hence "\<And>\<ii> p . p\<in>pathsInTree x \<Longrightarrow> (\<exists> r phead ptail rtail. (r = (hd r)#rtail) \<and> (p = phead#ptail) \<and> hd r |\<in>| (\<R> \<ii>) \<and> pathFitsListAndListIsARun \<ii> p r)"     using list.inject hd_Cons_tl
              by (metis list.simps(3))
            hence "\<And>\<ii> p . p\<in>pathsInTree x \<Longrightarrow> (\<exists> r phead ptail rtail. (r = (hd r)#rtail) \<and> (p = phead#ptail) \<and> hd r |\<in>| (\<R> \<ii>) \<and> pathFitsListAndListIsARun \<ii> p r \<and> labelOfNode phead = symbol (hd r))" 
              using pathFitsListAndListIsARun.simps(2)  by metis
            hence "\<And>\<ii> p . p\<in>pathsInTree x \<Longrightarrow> (\<exists> r phead ptail rtail. (r = (hd r)#rtail) \<and> (p = phead#ptail) \<and> hd r |\<in>| (\<R> \<ii>) \<and> pathFitsListAndListIsARun \<ii> p r \<and> (down phead) = x \<and> (labelOfNode phead = symbol (hd r)))"    
              using pathsInTree_def by fastforce
            hence "\<And>\<ii> p . p\<in>pathsInTree x \<Longrightarrow> (\<exists> r phead ptail rtail. (r = (hd r)#rtail) \<and> (p = phead#ptail) \<and> hd r |\<in>| (\<R> \<ii>) \<and> pathFitsListAndListIsARun \<ii> p r \<and> (down phead) = x \<and> (\<alpha> = symbol (hd r)))"
              using n645787 labelOfNode_def
              by (metis n766897) 
            hence "\<And>\<ii> p . p\<in>pathsInTree x \<Longrightarrow> (\<exists> r phead ptail rtail. ((hd r |\<in>| rulesPerAlpha \<alpha> \<ii>) \<and> (hd r |\<in>| (\<R> \<ii>) ) \<and> (r = (hd r)#rtail) \<and> (p = phead#ptail) \<and> hd r |\<in>| (\<R> \<ii>) \<and> pathFitsListAndListIsARun \<ii> p r \<and> (down phead) = x \<and> (\<alpha> = symbol (hd r))))"
              using rulesPerAlpha_def by fastforce
            hence n764654 : "\<And>\<ii> p . p\<in>pathsInTree x \<Longrightarrow> 
((pathSatisfiesApproximatorForRuleSet p (rulesPerAlpha \<alpha> \<ii>) \<ii>) \<and> (\<exists> r phead ptail rtail. ((hd r |\<in>| rulesPerAlpha \<alpha> \<ii>) \<and> (r = (hd r)#rtail) \<and> (p = phead#ptail) \<and> hd r |\<in>| (\<R> \<ii>) \<and> pathFitsListAndListIsARun \<ii> p r \<and> (down phead) = x \<and> (\<alpha> = symbol (hd r)))))"                      
              using pathSatisfiesApproximatorForRuleSet_def by fastforce
            hence "\<And>\<ii> . satisfiesApproximatorForRuleSet x (rulesPerAlpha \<alpha> \<ii>) \<ii>" using satisfiesApproximatorForRuleSet_def by blast
            hence n76454 : "x \<in> \<P> (rulesPerAlpha \<alpha>)" using \<P>_def by simp
            obtain path where n654e53 : "path \<in> pathsInTree x"            using theSingletonPathExists by auto 
            hence "\<And>\<ii> . (\<exists> rule . symbol rule = \<alpha> \<and> rule |\<in>| (\<R> \<ii>))" using n764654 by fastforce
            hence "(\<forall> \<ii> . \<alpha> |\<in>| fimage symbol (\<R> \<ii>))" by blast
            then show "x \<in> \<P> (rulesPerAlpha \<alpha>) \<and> (\<forall> \<ii> . \<alpha> |\<in>| fimage symbol (\<R> \<ii>))" using n76454 by auto
          qed
          hence n564rt8i7 : "\<alpha> |\<in>| (fimage symbol (\<R> \<aa>\<^sub>1) |\<union>| fimage symbol (\<R> \<aa>\<^sub>2))" by auto
              
          from n754654 \<ff>_def restrictionIsFinite restrictionIsFinite2 \<Z>\<^sub>\<tau>_def have "height x \<le> Suc n"            by (simp add: \<open>height x \<le> Suc n\<close>) 
              
              from n6545877 \<ff>_def restrictionIsFinite restrictionIsFinite2 \<Z>\<^sub>\<tau>_def have n656988 : "x |\<in>| (\<ff> (Suc n)  (rulesPerAlpha \<alpha>))"
                by (metis n754654 zIntersectLemma) 
                  
            from occurringAlphas_def show "\<alpha> |\<in>| occurringAlphas"  using n656988 n564rt8i7
              by (metis (mono_tags, lifting) bot_fset.rep_eq fempty_iff ffmember_filter notin_fset) 
          qed
            
                
          
        have "\<And> i . ({|x|} \<in> \<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i)) |`|  ((rulesPerAlpha \<alpha>) i)))))"
        proof -
          fix i
          from n766 obtain z1 z2 where q10 : "y = \<Psi>\<^sub>\<phi> z1" and q11 : "y = \<Psi>\<^sub>\<phi> z2" and q12 : "z1 \<in> (\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| ((\<R>) \<aa>\<^sub>1))))" and q13 : "z2 \<in> (\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>2) |`| ((\<R>) \<aa>\<^sub>2))))" using \<Psi>\<^sub>\<Sigma>\<^sub>\<rho>_def by blast
          from n766 obtain zi where q10 : "y = \<Psi>\<^sub>\<phi> zi" and q12 : "zi \<in> (\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i)) |`| ((\<R>) i))))" using \<Psi>\<^sub>\<Sigma>\<^sub>\<rho>_def \<A>.simps by (metis (full_types) \<open>\<And>thesis. (\<And>z1 z2. \<lbrakk>y = \<Psi>\<^sub>\<phi> z1; y = \<Psi>\<^sub>\<phi> z2; z1 \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1 |`| \<R> \<aa>\<^sub>1); z2 \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>2 |`| \<R> \<aa>\<^sub>2)\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> ot.exhaust)
              
          from q1 have n76898 : "x |\<in>| y" by auto
          from   q10 have n767988 : "y = \<Psi>\<^sub>\<phi> zi" by auto
          from q12 have nu6568 :  "zi \<in> (\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i)) |`| ((\<R>) i))))" by auto
          from psiF_def    have "\<Psi>\<^sub>\<phi> zi = fimage (\<lambda> symbol2 . psi (NODE symbol2 (\<Union>| (fimage childrenSet (childrenWithSymbol symbol2 zi)))))(fimage root zi)" by auto
          then obtain symbol2 where "symbol2 |\<in>| fimage root zi" and n76y8 : "x = psi (NODE symbol2 (\<Union>| (fimage childrenSet (childrenWithSymbol symbol2 zi))))"  using q1 q10 by fastforce 
          from n76y8 have "symbol2 = root x" using psiRoot root.simps         by (simp add: psiRoot) 
          then have n767988 : "symbol2 = \<alpha>" using \<alpha>_def by auto
          def childrenForTheSymbol == "(\<Union>| (fimage childrenSet (childrenWithSymbol \<alpha> zi)))"
          hence b76986 : "x = psi (NODE symbol2 childrenForTheSymbol)" using n767988 n76y8 by auto
          from nu6568 biguplusForests_def    have n767898 : "(\<And> tr . tr |\<in>| zi \<Longrightarrow> (\<exists> lang . lang |\<in>| ( (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i)) |`| ((\<R>) i))  )) \<and> (\<exists> (subforest) . (tr |\<in>| subforest \<and> subforest |\<subseteq>| zi \<and> subforest \<in> lang)))) " by blast
          def originalForest == "ffilter (\<lambda> tree . root tree = \<alpha>) zi"
          have "originalForest \<noteq> {||}" 
          proof 
            assume "originalForest = {||}" 
            then have "\<And>tr . tr |\<in>| zi \<Longrightarrow> root tr \<noteq> \<alpha>" using originalForest_def by auto
            then have "\<And>tr . tr |\<in>| y \<Longrightarrow> root tr \<noteq> \<alpha>" using n767988 psiDef   using \<open>symbol2 |\<in>| root |`| zi\<close> by fastforce 
            then show "False" using \<alpha>_def n76898 by auto
          qed
          have n879698 : "{|x|} = \<Psi>\<^sub>\<phi> originalForest"
          proof -
            from originalForest_def have "originalForest = ffilter (\<lambda> tree . root tree = \<alpha>) zi" by auto
            from b76986  have "x = psi (NODE symbol2 childrenForTheSymbol)" by auto
            from psiF_def have n767987 : "\<Psi>\<^sub>\<phi> originalForest = fimage (\<lambda> symbol2 . psi (NODE symbol2 (\<Union>| (fimage childrenSet (childrenWithSymbol symbol2 originalForest)))) ) (fimage root originalForest)" by auto
            from originalForest_def   have n655687 : "(fimage root originalForest) |\<subseteq>| {|\<alpha>|}"               using fimage_fsubsetI by auto 
            from n767987 n655687 have n65787 : "\<Psi>\<^sub>\<phi> originalForest |\<subseteq>|  (finsert ( psi (NODE \<alpha> (\<Union>| (fimage childrenSet (childrenWithSymbol \<alpha> originalForest)))   )) fempty)"              by blast 
            then have n656899 : "\<Psi>\<^sub>\<phi> originalForest = (finsert ( psi (NODE \<alpha> (\<Union>| (fimage childrenSet (childrenWithSymbol \<alpha> originalForest)))   )) fempty)" using n65787 using fsubset_fsingletonD n767987 using \<open>originalForest \<noteq> {||}\<close> by fastforce 
            have "psi (NODE \<alpha> (\<Union>| (fimage childrenSet (childrenWithSymbol \<alpha> originalForest)))   ) = x"
            proof -
              from b76986    have "x = psi (NODE symbol2 childrenForTheSymbol)" by auto
              then have "x = NODE symbol2 (fimage (\<lambda> symbol2 .psi (NODE symbol2 (\<Union>| (fimage childrenSet (childrenWithSymbol symbol2 childrenForTheSymbol)))))(fimage root childrenForTheSymbol))" 
                using psiDef by blast
              then have "x = NODE \<alpha> (fimage (\<lambda> symbol2 . psi (NODE symbol2 (\<Union>| (fimage childrenSet (childrenWithSymbol symbol2 childrenForTheSymbol)))))(fimage root childrenForTheSymbol))" 
                using n767988 by auto
              def childrenSelected == "(\<Union>| (fimage childrenSet (childrenWithSymbol \<alpha> originalForest)))"
              have "psi (NODE \<alpha>  childrenSelected  ) = NODE \<alpha> (fimage (\<lambda> symbol2 .psi (NODE symbol2 (\<Union>| (fimage childrenSet (childrenWithSymbol symbol2 childrenSelected)))))(fimage root childrenSelected))" 
                using psiDef childrenSelected_def by blast
              have "childrenWithSymbol \<alpha> originalForest = childrenWithSymbol \<alpha> zi"
              proof
                show "childrenWithSymbol \<alpha> originalForest |\<subseteq>| childrenWithSymbol \<alpha> zi" using originalForest_def childrenWithSymbol_def          by (metis ffmember_filter finterD1 finterI fsubsetI mem_Collect_eq) 
                show "childrenWithSymbol \<alpha> zi |\<subseteq>| childrenWithSymbol \<alpha> originalForest"  
                proof 
                  fix x
                  assume "x |\<in>| childrenWithSymbol \<alpha> zi"
                  then have "x |\<in>| inf_fset2 zi {child1. root child1 = \<alpha>}" using childrenWithSymbol_def                         by (simp add: childrenWithSymbol_def) 
                  then show "x |\<in>| childrenWithSymbol \<alpha> originalForest"  using childrenWithSymbol_def    originalForest_def by (metis Int_iff ffmember_filter finterD1 inf_fset2.rep_eq mem_Collect_eq notin_fset) 
                qed      
              qed
              then have "childrenSelected = childrenForTheSymbol" using childrenSelected_def childrenForTheSymbol_def originalForest_def childrenWithSymbol_def by auto
              then have "((fimage (\<lambda> symbol2 .   psi (NODE symbol2 (\<Union>| (fimage childrenSet (childrenWithSymbol symbol2 childrenSelected)))))(fimage root childrenSelected))) = ((fimage (\<lambda> symbol2 .psi (NODE symbol2 (\<Union>| (fimage childrenSet (childrenWithSymbol symbol2 childrenForTheSymbol))))) (fimage root childrenForTheSymbol)))" by auto
              then show "psi (NODE \<alpha> (\<Union>| (fimage childrenSet (childrenWithSymbol \<alpha> originalForest)))   ) = x"                     using \<open>psi (NODE \<alpha> childrenSelected) = NODE \<alpha> ((\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 childrenSelected)))) |`| root |`| childrenSelected)\<close> \<open>x = NODE \<alpha> ((\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 childrenForTheSymbol)))) |`| root |`| childrenForTheSymbol)\<close> childrenSelected_def by auto 
            qed
            then show "{|x|} = \<Psi>\<^sub>\<phi> originalForest"                     by (simp add: n656899) 
          qed
          from n767898 originalForest_def have  "(\<And> tr . tr |\<in>| originalForest \<Longrightarrow> (\<exists> lang . lang |\<in>| ( (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i)) |`| ((rulesPerAlpha \<alpha>) i))  )) \<and> (\<exists> (subforest) . (tr |\<in>| subforest \<and> subforest |\<subseteq>| originalForest \<and> subforest \<in> lang)))) "
          proof -
            fix tr
            assume n756988 : "tr |\<in>| originalForest"
            then have n76y8o7 : "tr |\<in>| zi" using originalForest_def
              by auto 
            from n767898 n767898 obtain lang subforest where n7686789 : "lang |\<in>| ( (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i)) |`| ((\<R>) i))  ))" and n76809 : "tr |\<in>| subforest"  and n6577 : "subforest |\<subseteq>| zi" and  n65709 : "subforest \<in> lang" by (meson n76y8o7) 
                
            def newSubforest == "originalForest |\<inter>| subforest"
            from n76809 newSubforest_def n756988 have y62 : "tr |\<in>| newSubforest" by auto
            from n6577  newSubforest_def  have "newSubforest |\<subseteq>| zi" by auto
            from n7686789 n65709 forest_language_for_rule_def obtain rule where n76798 : "rule |\<in>| ((\<R>) i)" and "\<And> tree.(tree|\<in>|subforest \<longrightarrow>  tree_for_rule (\<A> i) rule tree) \<and> (\<exists> tree. tree |\<in>| subforest)" and n76988 : "lang = \<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) rule" by blast
            then have "tree_for_rule (\<A> i) rule tr" using n76809 by auto
            then have "root tr = symbol rule" using tree_for_rule_def by auto
            then have n76698 : "symbol rule = \<alpha>" using originalForest_def n756988 by auto
            then have n75656988 : "rule |\<in>| ((rulesPerAlpha \<alpha>) i)" using n76798 rulesPerAlpha_def by auto 
            from n76698  n76988 n75656988 rulesPerAlpha_def have y60 : "lang |\<in>| ((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i)) |`| ((rulesPerAlpha \<alpha>) i))" by auto
            have  y61 :"newSubforest \<in> lang" 
            proof -
              from n76988 have n76988 : "lang = \<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) rule" by auto
              have "(\<forall>tree.(tree|\<in>|newSubforest \<longrightarrow>  tree_for_rule (\<A> i) rule tree)) \<and> (\<exists> tree. tree |\<in>| newSubforest)" using  y62 newSubforest_def n76988 n65709 using \<open>\<And>tree. (tree |\<in>| subforest \<longrightarrow> tree_for_rule (\<A> i) rule tree) \<and> (\<exists>tree. tree |\<in>| subforest)\<close> by auto
              then have "newSubforest \<in> \<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) rule" using forest_language_for_rule_def by auto
              then show "newSubforest \<in> lang"  using n76988 by auto
            qed
            from y60 y61 y62 newSubforest_def have "lang |\<in>| ( (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i)) |`| ((rulesPerAlpha \<alpha>) i))  ))" and "tr |\<in>| newSubforest" and "newSubforest |\<subseteq>| originalForest" and "newSubforest \<in> lang" by auto
            then show "(\<exists> lang . lang |\<in>| ( (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i)) |`| ((rulesPerAlpha \<alpha>) i))  )) \<and> (\<exists> (subforest) . (tr |\<in>| subforest \<and> subforest |\<subseteq>| originalForest \<and> subforest \<in> lang)))"       by blast 
          qed
          then show "{|x|} \<in> \<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i)) |`|  ((rulesPerAlpha \<alpha>) i))))" using n879698 biguplusForests_def by auto
        qed
        then have nu676798 : "{|x|} \<in> (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> ((((rulesPerAlpha \<alpha>)) \<aa>\<^sub>1))(((((rulesPerAlpha \<alpha>)) \<aa>\<^sub>2))))" using \<Psi>\<^sub>\<Sigma>\<^sub>\<rho>_def  by (metis (full_types) IntI \<A>.simps(1) \<A>.simps(2)) 
            
        have "x |\<in>| bounded (Suc n)" by (simp add: \<open>height x \<le> Suc n\<close> restrictionIsFinite2)
            
        have "\<And>y . y |\<in>| {|x|} \<Longrightarrow> height y \<le> Suc n" using fsingletonD restrictionIsFinite notin_fset  using \<open>height x \<le> Suc n\<close> by blast 
        then have "{|x|} \<in> (fset (boundedForests (Suc n)))" using restrictionIsFiniteForests by blast
        then have "{|x|} |\<in>| boundedForests (Suc n)" using notin_fset by fastforce
        then have n76689u : "{|x|} |\<in>| (\<Z>\<^sub>\<phi> (Suc n) (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (((((rulesPerAlpha \<alpha>)) \<aa>\<^sub>1)))((((rulesPerAlpha \<alpha>) \<aa>\<^sub>2)))))" using nu676798 \<Z>\<^sub>\<phi>_def by blast
        from n64r57689 show "x |\<in>| \<Union>| (gAlpha |`| occurringAlphas)" using n76689u gAlpha_def using \<gg>_def by auto 
      qed
        
      show "\<Pi>\<^sub>\<tau>\<^sub>F (\<gg> (Suc n) \<R>) \<subseteq> (\<Union>\<alpha>\<in>fset occurringAlphas. \<Pi>\<^sub>\<tau>\<^sub>F (gAlpha \<alpha>))" 
      proof
        fix x
        assume n768 :  "x \<in> \<Pi>\<^sub>\<tau>\<^sub>F (\<gg> (Suc n) \<R>)"
        from n767988 have "((\<gg> (Suc n) \<R>)) |\<subseteq>| \<Union>|((\<lambda>\<alpha>. ((gAlpha \<alpha>))) |`|  occurringAlphas)" by auto
        then have "x \<in> \<Pi>\<^sub>\<tau>\<^sub>F (\<Union>|((\<lambda>\<alpha>. ((gAlpha \<alpha>))) |`|  occurringAlphas))" using n768  by (meson less_eq_fset.rep_eq pathsTreeLangMonotone subsetCE) 
        then obtain \<alpha> where "\<alpha> |\<in>| occurringAlphas" and "x \<in> \<Pi>\<^sub>\<tau>\<^sub>F (((gAlpha \<alpha>)))"
        proof -
          assume a1: "\<And>\<alpha>. \<lbrakk>\<alpha> |\<in>| occurringAlphas; x \<in> \<Pi>\<^sub>\<tau>\<^sub>F (gAlpha \<alpha>)\<rbrakk> \<Longrightarrow> thesis"
          have f2: "x |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Union>| (gAlpha |`| occurringAlphas))"
            using \<open>x \<in> \<Pi>\<^sub>\<tau>\<^sub>F (\<Union>| (gAlpha |`| occurringAlphas))\<close> notin_fset piFset by fastforce
          obtain tt :: "abc tree fset \<Rightarrow> abc list \<Rightarrow> abc tree" where
            f3: "\<forall>as f. (as |\<notin>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> f \<or> tt f as |\<in>| f \<and> as |\<in>| \<delta>\<^sub>\<tau> (tt f as)) \<and> (as |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> f \<or> (\<forall>t. t |\<notin>| f \<or> as |\<notin>| \<delta>\<^sub>\<tau> t))"
            by (metis pathsTreeForest)
          obtain aa :: "(abc \<Rightarrow> bool) \<Rightarrow> abc fset \<Rightarrow> abc" where
            f4: "\<forall>x0 x1. (\<exists>v2. v2 |\<in>| x1 \<and> x0 v2) = (aa x0 x1 |\<in>| x1 \<and> x0 (aa x0 x1))"
            by moura
          obtain ff :: "abc tree fset fset \<Rightarrow> abc tree \<Rightarrow> abc tree fset" where
            "\<forall>x0 x1. (\<exists>v2. v2 |\<in>| x0 \<and> x1 |\<in>| v2) = (ff x0 x1 |\<in>| x0 \<and> x1 |\<in>| ff x0 x1)"
            by moura
          then have f5: "\<forall>t f. t |\<notin>| \<Union>| f \<or> ff f t |\<in>| f \<and> t |\<in>| ff f t"
            by (meson ffUnionLemma)
          then have "fBex occurringAlphas (\<lambda>a. ff (gAlpha |`| occurringAlphas) (tt (\<Union>| (gAlpha |`| occurringAlphas)) x) = gAlpha a)"
            using f3 f2 by (metis (no_types) fimage_iff)
          then have f6: "aa (\<lambda>a. ff (gAlpha |`| occurringAlphas) (tt (\<Union>| (gAlpha |`| occurringAlphas)) x) = gAlpha a) occurringAlphas |\<in>| occurringAlphas \<and> ff (gAlpha |`| occurringAlphas) (tt (\<Union>| (gAlpha |`| occurringAlphas)) x) = gAlpha (aa (\<lambda>a. ff (gAlpha |`| occurringAlphas) (tt (\<Union>| (gAlpha |`| occurringAlphas)) x) = gAlpha a) occurringAlphas)"
            using f4 by (meson fBexE)
          then have "tt (\<Union>| (gAlpha |`| occurringAlphas)) x |\<in>| gAlpha (aa (\<lambda>a. ff (gAlpha |`| occurringAlphas) (tt (\<Union>| (gAlpha |`| occurringAlphas)) x) = gAlpha a) occurringAlphas)"
            using f5 f3 f2 by presburger
          then show ?thesis
            using f6 f3 f2 a1 by (metis (no_types) notin_fset piFset)
        qed
        then show "x \<in> (\<Union>\<alpha>\<in>fset occurringAlphas. \<Pi>\<^sub>\<tau>\<^sub>F (gAlpha \<alpha>))" by (meson UN_iff notin_fset) 
      qed
    qed
  qed
   from u1 u2 u3 show "\<Pi>\<^sub>\<tau>\<^sub>F (\<ff> (Suc n) \<R>) = \<Pi>\<^sub>\<tau>\<^sub>F (\<gg> (Suc n) \<R>)" using notin_fset by fastforce
qed


  
lemma core_main_lemma_conclusion :
  fixes l
  fixes \<R>
  fixes n
  fixes j
  assumes "\<And> \<R>  r i. (r |\<in>| \<R> i \<Longrightarrow> (r |\<in>| rule_set (\<A> i)))"
  assumes statesLanguagesNonempty : "\<And> \<R> i r . (r |\<in>| (\<R> i) \<Longrightarrow>  (\<And> s . (s |\<in>| (states r) \<Longrightarrow> ((\<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> i) s)  \<noteq> {}))))"
  assumes inStateSet : "\<And> \<R> \<ii> r  s . (r |\<in>| (\<R> \<ii>) \<Longrightarrow> s |\<in>| states r \<Longrightarrow> s |\<in>| state_set (\<A> \<ii>))"
  assumes    rulesLangsNonempty : "\<And> \<R> i r . (r |\<in>| rule_set (\<A> i) \<Longrightarrow>  ((\<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) r)  \<noteq> {}))"
    assumes allRulesArePresent : "(\<And>i rule. rule |\<in>| rule_set (\<A> i))"
  shows "\<And>\<R> . ((\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> n  \<R>))) = \<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> n \<R>)))"
proof (induct n)
  case 0
  have "\<And>\<R>. (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> 0  \<R>))) = \<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> 0 \<R>))"
  proof -
    fix \<R>
    have "\<And> tr . \<exists>z . height tr = Suc z" 
    proof -
      fix tr
      show "\<exists>z . height tr = Suc z"
      proof (induct tr)
        case (NODE x1a x2a)
        from height_def obtain val where "height (NODE x1a x2a) = 1 + val"            by simp
        then show ?case by auto
      qed
    qed
    then have h7656787  : "\<And>x y. x |\<notin>| \<Z>\<^sub>\<tau> 0 y" using \<Z>\<tau>_lemma Z_def        by (metis (no_types, lifting) le_0_eq mem_Collect_eq notin_fset old.nat.distinct(2))
    then  have n655676 : "(\<ff> 0  \<R>) = {||}" 
    proof -
      assume "\<And>x y. x |\<notin>| \<Z>\<^sub>\<tau> 0 y"
      then show "\<ff> 0 \<R> = {||}"
        using \<ff>_def by blast
    qed
    from h7656787 have  n76587 : "(\<gg> 0 \<R>) = {||}" using \<gg>_def  by (metis assms \<P>_def \<ff>_def all_not_fin_conv antisym_conv fsubsetI gInF) 
    from n655676 have a1 : "(\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> 0  \<R>))) = {}" using pathsForTreeLanguage_def        by auto
    from n76587 have a2 : "\<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> 0 \<R>)) = {}"  using pathsForTreeLanguage_def       by auto
    from a1 a2 show "(\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> 0  \<R>))) = \<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> 0 \<R>))" by blast
  qed
  then show ?case by auto
next
  case (Suc n)
  show ?case
  proof (rule disjE)
    show "fset (\<ff> (Suc n)  \<R>) \<noteq> {} \<or>fset (\<ff> (Suc n)  \<R>) = {} " by auto
    show "fset (\<ff> (Suc n) \<R>) = {} \<Longrightarrow> \<Pi>\<^sub>\<tau>\<^sub>F (\<ff> (Suc n) \<R>) = \<Pi>\<^sub>\<tau>\<^sub>F (\<gg> (Suc n) \<R>)"
    proof -
      assume n76a5677 : "fset (\<ff> (Suc n) \<R>) = {}"
      then have n654588 :  "fset (\<gg> (Suc n) \<R>) = {}" using \<P>_def \<ff>_def all_not_fin_conv antisym_conv fsubsetI gInF  \<gg>_def          by (metis assms bot.extremum_uniqueI less_eq_fset.rep_eq) 
      from n76a5677   have a1 : "(\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n)  \<R>))) = {}" using pathsForTreeLanguage_def        by auto
      from n654588   have a2 : "(\<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> (Suc n)  \<R>))) = {}" using pathsForTreeLanguage_def        by auto
      from a1 a2 show "\<Pi>\<^sub>\<tau>\<^sub>F (\<ff> (Suc n) \<R>) = \<Pi>\<^sub>\<tau>\<^sub>F (\<gg> (Suc n) \<R>)" by auto
    qed
    show "fset (\<ff> (Suc n) \<R>) \<noteq> {} \<Longrightarrow> \<Pi>\<^sub>\<tau>\<^sub>F (\<ff> (Suc n) \<R>) = \<Pi>\<^sub>\<tau>\<^sub>F (\<gg> (Suc n) \<R>)"
    proof (rule disjE)
      show "Suc n > \<N> \<or> Suc n \<le> \<N>" by linarith
      assume n655688 : "fset (\<ff> (Suc n) \<R>) \<noteq> {}"
      {
        assume n54764 : "Suc n > \<N>"
        have "    (\<And>\<ii> r s. r |\<in>| \<R> \<ii> \<Longrightarrow> s |\<in>| states r \<Longrightarrow> \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>) s \<noteq> {}) \<Longrightarrow>     (\<And>rs2. \<Pi>\<^sub>\<tau>\<^sub>F (\<ff> n rs2) = \<Pi>\<^sub>\<tau>\<^sub>F (\<gg> n rs2)) \<Longrightarrow> (\<And>\<ii> r s. r |\<in>| \<R> \<ii> \<Longrightarrow> s |\<in>| states r \<Longrightarrow> s |\<in>| state_set (\<A> \<ii>)) \<Longrightarrow> \<N> < Suc n \<Longrightarrow> \<Pi>\<^sub>\<tau>\<^sub>F (\<ff> (Suc n) \<R>) = \<Pi>\<^sub>\<tau>\<^sub>F (\<gg> (Suc n) \<R>)"            using core_main_lemma4 n655688 assms   Suc.hyps  by auto
        hence "    (\<And>\<ii> r s. r |\<in>| \<R> \<ii> \<Longrightarrow> s |\<in>| states r \<Longrightarrow> \<L>\<^sub>\<phi>\<^sub>\<sigma> (\<A> \<ii>) s \<noteq> {}) \<Longrightarrow>      (\<And>\<ii> r s. r |\<in>| \<R> \<ii> \<Longrightarrow> s |\<in>| states r \<Longrightarrow> s |\<in>| state_set (\<A> \<ii>))  \<Longrightarrow> \<Pi>\<^sub>\<tau>\<^sub>F (\<ff> (Suc n) \<R>) = \<Pi>\<^sub>\<tau>\<^sub>F (\<gg> (Suc n) \<R>)"            using assms  n54764 Suc.hyps   by auto
        hence "      (\<And>\<ii> r s. r |\<in>| \<R> \<ii> \<Longrightarrow> s |\<in>| states r \<Longrightarrow> s |\<in>| state_set (\<A> \<ii>))  \<Longrightarrow> \<Pi>\<^sub>\<tau>\<^sub>F (\<ff> (Suc n) \<R>) = \<Pi>\<^sub>\<tau>\<^sub>F (\<gg> (Suc n) \<R>)"            using assms(2)      by fastforce
        then show " \<Pi>\<^sub>\<tau>\<^sub>F (\<ff> (Suc n) \<R>) = \<Pi>\<^sub>\<tau>\<^sub>F (\<gg> (Suc n) \<R>)"            using assms(3)     by fastforce
      }
      {
        assume n7568 : "Suc n \<le> \<N> "
        show "((\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n)  \<R>))) = \<Pi>\<^sub>\<tau>\<^sub>F ((\<gg> (Suc n) \<R>)))" 
        proof
          from smallerThanN n7568 have n546687 : "\<And>f \<ii>. (                          f |\<in>| (\<Z>\<^sub>\<tau> (Suc n) (\<P>\<^sub>1 \<R> \<ii>)) \<Longrightarrow>                        \<Pi> f \<in> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (((\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>)) |`| (\<R> \<ii>)))))))" by auto
          then show "\<Pi>\<^sub>\<tau>\<^sub>F (\<ff> (Suc n) \<R>) \<subseteq> \<Pi>\<^sub>\<tau>\<^sub>F (\<gg> (Suc n) \<R>)"                   
          proof -
            have "\<And>x . x \<in> \<Pi>\<^sub>\<tau>\<^sub>F (\<ff> (Suc n) \<R>) \<Longrightarrow> x \<in> \<Pi>\<^sub>\<tau>\<^sub>F (\<gg> (Suc n) \<R>)" 
            proof -
              fix x
              assume "x \<in> \<Pi>\<^sub>\<tau>\<^sub>F (\<ff> (Suc n) \<R>)"
              then obtain tr where n7896 : "tr |\<in>| (\<ff> (Suc n) \<R>)" and n6578 : "x |\<in>| \<Pi> tr" using pathsForTreeLanguage_def                      by (metis notin_fset pathsTreeForest piFset)
              then have n5787 : "\<And>  \<ii> . tr |\<in>| (\<Z>\<^sub>\<tau> (Suc n) (\<P>\<^sub>1 \<R> \<ii>))" using \<ff>_def \<P>_def
              proof -
                fix \<ii> :: ot
                have "tr \<in> {t. \<forall>z. satisfiesApproximatorForRuleSet t (\<R> z) z}"                          by (metis (no_types) \<P>_def \<ff>_def \<open>tr |\<in>| \<ff> (Suc n) \<R>\<close> zIntersectLemma)
                then have "tr \<in> {t. satisfiesApproximatorForRuleSet t (\<R> \<ii>) \<ii>}"                          by blast
                then show "tr |\<in>| \<Z>\<^sub>\<tau> (Suc n) (\<P>\<^sub>1 \<R> \<ii>)"                          by (metis (no_types) \<P>\<^sub>1_def \<ff>_def \<open>tr |\<in>| \<ff> (Suc n) \<R>\<close> zIntersectLemma)
              qed 
              then have n548761 : "\<And>  \<ii>. \<Pi> tr \<in> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (((\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>)) |`| (\<R> \<ii>))))))"  using n546687                          by simp
                  
              have n5458779 : "\<And>  \<ii>. \<Pi> tr \<in> \<Pi>\<^sub>\<iota>\<^sub>\<phi> `( ((\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>)) |`| (\<R> \<ii>)))))))"  
              proof -
                fix \<ii>
                from n548761  have "\<Pi> tr \<in> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (((\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>)) |`| (\<R> \<ii>))))))" by auto
                then obtain otherForest where "otherForest \<in> (((\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>)) |`| (\<R> \<ii>))))))" and n65787 : "\<Pi> tr = \<Pi>\<^sub>\<iota>\<^sub>\<phi> otherForest"                              by blast 
                then have "\<Psi>\<^sub>\<phi> otherForest \<in> ( ((\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>)) |`| (\<R> \<ii>)))))))" by auto
                then have "\<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> otherForest) \<in> \<Pi>\<^sub>\<iota>\<^sub>\<phi> `( ((\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>)) |`| (\<R> \<ii>)))))))" by auto
                then show "\<Pi> tr \<in> \<Pi>\<^sub>\<iota>\<^sub>\<phi> `( ((\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>)) |`| (\<R> \<ii>)))))))" using n65787 psiPreservesPaths by auto 
              qed
              from n548761  have r1 : "\<Pi> tr \<in> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (((\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<aa>\<^sub>1)) |`| (\<R> \<aa>\<^sub>1))))))" by blast
              from n548761  have r2 : "\<Pi> tr \<in> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (((\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<aa>\<^sub>2)) |`| (\<R> \<aa>\<^sub>2))))))"  by blast
              from r1 obtain otherForest1 where s1 : "otherForest1 \<in> (((\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<aa>\<^sub>1)) |`| (\<R> \<aa>\<^sub>1))))))" and n657871 : "\<Pi> tr = \<Pi>\<^sub>\<iota>\<^sub>\<phi> otherForest1"                              by blast 
              from r2 obtain otherForest2 where s2 : "otherForest2 \<in> (((\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<aa>\<^sub>2)) |`| (\<R> \<aa>\<^sub>2))))))" and n657872 : "\<Pi> tr = \<Pi>\<^sub>\<iota>\<^sub>\<phi> otherForest2"                              by blast 
              from n657871 n657872 have "\<Pi>\<^sub>\<iota>\<^sub>\<phi> otherForest1 = \<Pi>\<^sub>\<iota>\<^sub>\<phi> otherForest2" by auto
              then have n237678 : "\<Psi>\<^sub>\<phi> otherForest1 = \<Psi>\<^sub>\<phi> otherForest2" using psiOnlyDependsOnPath by blast
              from s1 n237678 have t1 : "\<Psi>\<^sub>\<phi> otherForest1 \<in> ( ((\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<aa>\<^sub>1)) |`| (\<R> \<aa>\<^sub>1)))))))" by auto
              from s2 n237678 have t2 : "\<Psi>\<^sub>\<phi> otherForest1 \<in> ( ((\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<aa>\<^sub>2)) |`| (\<R> \<aa>\<^sub>2)))))))" by auto
              have n65897764 : "\<Pi> tr = \<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> otherForest1)"  by (simp add: n657871 psiPreservesPaths) 
              from t1 t2 have n5458098 : "\<Psi>\<^sub>\<phi> otherForest1 \<in> ( ((\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<aa>\<^sub>1)) |`| (\<R> \<aa>\<^sub>1))))))) \<inter> ( ((\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<aa>\<^sub>2)) |`| (\<R> \<aa>\<^sub>2)))))))" by auto
              from n7896  \<ff>_def \<Z>\<tau>_lemma Z_def notin_fset have "tr \<in> Z (Suc n) (\<P> \<R>)"                                               by metis
              then  have n5434679 : "height tr \<le> Suc n" using Z_def by blast
              have "\<And> tree . tree |\<in>| \<Psi>\<^sub>\<phi> otherForest1 \<Longrightarrow> height tree \<le> Suc n"
              proof -
                fix tree
                assume "tree |\<in>| \<Psi>\<^sub>\<phi> otherForest1"
                then  have "\<Pi> tree |\<subseteq>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> otherForest1)"                        by (meson fsubsetI pathsTreeForest)
                then have "\<Pi> tree |\<subseteq>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> otherForest1)" using n65897764 by auto
                then have "\<Pi> tree |\<subseteq>| \<Pi> tr" using n657871  n65897764 by auto
                then show "height tree  \<le> Suc n" using n5434679 heightOnlyDependsOnPaths                            by (metis dual_order.trans fimage_mono maxMonotonic) 
              qed
              then have n656798 : "\<Psi>\<^sub>\<phi> otherForest1 |\<in>| (((\<Z>\<^sub>\<phi> (Suc n) ((((\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<aa>\<^sub>1)) |`| (\<R> \<aa>\<^sub>1)))))))\<inter> ( ((\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<aa>\<^sub>2)) |`| (\<R> \<aa>\<^sub>2)))))))))))"
              proof -
                assume "\<And>tree. tree |\<in>| \<Psi>\<^sub>\<phi> otherForest1 \<Longrightarrow> height tree \<le> Suc n"
                then have "\<Psi>\<^sub>\<phi> otherForest1 \<in> fset (boundedForests (Suc n))"                        by (simp add: restrictionIsFiniteForests)
                then have "\<Psi>\<^sub>\<phi> otherForest1 |\<in>| boundedForests (Suc n)"                        by (meson notin_fset)
                then show ?thesis                        using \<Z>\<^sub>\<phi>_def n5458098 by blast
              qed 
              then have n656798b : "\<Psi>\<^sub>\<phi> otherForest1 |\<subseteq>| \<Union>| (\<Z>\<^sub>\<phi> (Suc n) ( ((\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| (\<R> \<aa>\<^sub>1)))))        \<inter> (\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>2) |`| (\<R> \<aa>\<^sub>2))))))))"      by auto
              then have n656798c : "(\<Pi> |`|  (\<Psi>\<^sub>\<phi> otherForest1)) |\<subseteq>| (\<Pi> |`|  (\<Union>| (\<Z>\<^sub>\<phi> (Suc n) ( ((\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| (\<R> \<aa>\<^sub>1)))))       \<inter> (\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>2) |`| (\<R> \<aa>\<^sub>2))))))))))" by auto
              from n6578  n657871 pathsTreeForest obtain tree3 where ni866 : "x |\<in>| \<Pi> tree3" and "tree3 |\<in>| (\<Psi>\<^sub>\<phi> otherForest1)"                          by (metis n65897764)
              then have n65898 : "\<Pi> tree3 |\<in>| (\<Pi> |`|  (\<Union>| (\<Z>\<^sub>\<phi> (Suc n) ( ((\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| (\<R> \<aa>\<^sub>1)))))       \<inter> (\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>2) |`| (\<R> \<aa>\<^sub>2))))))))))" using n656798c                          by blast 
              from \<gg>_def \<Psi>\<^sub>\<Sigma>\<^sub>\<rho>_def have n54643 : " \<Pi>\<^sub>\<tau>\<^sub>F (\<gg> (Suc n) \<R>) =  \<Pi>\<^sub>\<tau>\<^sub>F (\<Union>| (\<Z>\<^sub>\<phi> (Suc n) ( ((\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| (\<R> \<aa>\<^sub>1)))))    \<inter> (\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>2) |`| (\<R> \<aa>\<^sub>2)))))))))" by auto
              from n65898 ni866 pathsForTreeLanguage_def have "x \<in> \<Pi>\<^sub>\<tau>\<^sub>F (\<Union>| (\<Z>\<^sub>\<phi> (Suc n) ( ((\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1) |`| (\<R> \<aa>\<^sub>1)))))      \<inter> (\<Psi>\<^sub>\<phi> `(\<Uplus> (((\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>2) |`| (\<R> \<aa>\<^sub>2)))))))))"     by (metis (mono_tags, lifting) \<open>tree3 |\<in>| \<Psi>\<^sub>\<phi> otherForest1\<close> less_eq_fset.rep_eq mem_Collect_eq n656798b notin_fset subsetCE)
              then show "x \<in> \<Pi>\<^sub>\<tau>\<^sub>F (\<gg> (Suc n) \<R>)" using n54643 by auto
            qed
            then show "\<Pi>\<^sub>\<tau>\<^sub>F (\<ff> (Suc n) \<R>) \<subseteq> \<Pi>\<^sub>\<tau>\<^sub>F (\<gg> (Suc n) \<R>)"    by auto
          qed
          show "\<Pi>\<^sub>\<tau>\<^sub>F (\<gg> (Suc n) \<R>) \<subseteq> \<Pi>\<^sub>\<tau>\<^sub>F (\<ff> (Suc n) \<R>)"                    by (metis assms \<gg>_def gInF less_eq_fset.rep_eq pathsTreeLangMonotone) 
        qed
      }
    qed
  qed
qed
  
    
end
  
    
  (*
  (* maybe showing this here is easier after all ... *)
  
  from UnionPathsInOut psiPiIntersection have n649853 : "\<Pi>\<^sub>\<phi> ( (\<Z>\<^sub>\<phi>\<^sub>F n ((\<Psi>\<^sub>\<phi> ` (\<Uplus> (S1))) \<inter> (\<Psi>\<^sub>\<phi> `(\<Uplus> (S2)))))) = \<Pi>\<^sub>\<delta> (fset (\<Z>\<^sub>\<delta> n (( (\<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S1))) \<inter> ((\<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S2))))))" sorry
      
  from assms(1) have  "\<And> l . l |\<in>| ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S1) \<Longrightarrow> closedUnderPlusD (l)" using closedAndP by auto
  from assms(2) have  "\<And> l . l |\<in>| ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S2) \<Longrightarrow> closedUnderPlusD (l)" using closedAndP by auto
  from assms(3)  have "\<And>l . l |\<in>| ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S1) \<Longrightarrow> l \<noteq> {}" by blast
  from assms(4) have "\<And>l . l |\<in>| ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S2) \<Longrightarrow> l \<noteq> {}"
    by blast 
  from assms(6)  have "\<And> l. (l |\<in>| (((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S1)) \<Longrightarrow> realizedInD l \<ff>)" using realizedInD_def realizedInForest_def
    by (metis (no_types, lifting) fimageE image_eqI) 
  from assms(7)  have "\<And> l. (l |\<in>| (((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S2)) \<Longrightarrow> realizedInD l \<ff>)" using realizedInD_def realizedInForest_def
    by (metis (no_types, lifting) fimageE image_eqI) 
      
  from realizationLemmaD have " (\<And>l. l |\<in>| ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S1) \<Longrightarrow> closedUnderPlusD l) \<Longrightarrow>
  (\<And>l. l |\<in>| ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S2) \<Longrightarrow> closedUnderPlusD l) \<Longrightarrow>
  (\<And>l. l |\<in>| ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S1) \<Longrightarrow> l \<noteq> {}) \<Longrightarrow>
  (\<And>l. l |\<in>| ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S2) \<Longrightarrow> l \<noteq> {}) \<Longrightarrow>
  (\<And>l. l |\<in>| ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S1) \<Longrightarrow> realizedInD l (UNION (fset (\<Z>\<^sub>\<delta> n (\<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S1) \<inter> \<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S2)))) fset)) \<Longrightarrow>
  (\<And>l. l |\<in>| ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S2) \<Longrightarrow> realizedInD l (UNION (fset (\<Z>\<^sub>\<delta> n (\<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S1) \<inter> \<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S2)))) fset)) \<Longrightarrow> 
UNION (fset (\<Z>\<^sub>\<delta> n (\<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S1) \<inter> \<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S2)))) fset = UNION (fset (\<Z>\<^sub>\<delta> n (\<Oplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S1) \<inter> \<Oplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S2)))) fset " by auto
  hence "UNION (fset (\<Z>\<^sub>\<delta> n (\<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S1) \<inter> \<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S2)))) fset = UNION (fset (\<Z>\<^sub>\<delta> n (\<Oplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S1) \<inter> \<Oplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S2)))) fset"
    using \<open>\<And>l. l |\<in>| op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| S1 \<Longrightarrow> closedUnderPlusD l\<close> \<open>\<And>l. l |\<in>| op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| S1 \<Longrightarrow> l \<noteq> {}\<close> \<open>\<And>l. l |\<in>| op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| S1 \<Longrightarrow> realizedInD l \<ff>\<close> \<open>\<And>l. l |\<in>| op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| S2 \<Longrightarrow> closedUnderPlusD l\<close> \<open>\<And>l. l |\<in>| op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| S2 \<Longrightarrow> l \<noteq> {}\<close> \<open>\<And>l. l |\<in>| op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| S2 \<Longrightarrow> realizedInD l \<ff>\<close> \<open>\<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` \<Uplus> S1 \<inter> \<Psi>\<^sub>\<phi> ` \<Uplus> S2)) = UNION (fset (\<Z>\<^sub>\<delta> n (\<Uplus>\<^sub>\<delta> (op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| S1) \<inter> \<Uplus>\<^sub>\<delta> (op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| S2)))) fset\<close> local.\<ff>_def by auto 
  hence nu6453 : "\<ff> = \<Pi>\<^sub>\<delta> (fset (\<Z>\<^sub>\<delta> n (( (\<Oplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S1))) \<inter> ((\<Oplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S2))))))" using assms(5) n649853 by auto
      
  have "\<Pi>\<^sub>\<delta> (fset (\<Z>\<^sub>\<delta> n (( (\<Oplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S1))) \<inter> ((\<Oplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| S2)))))) = \<Pi>\<^sub>\<phi> ( (\<Z>\<^sub>\<phi>\<^sub>F n ((\<Psi>\<^sub>\<phi> `(\<Oplus> (S1))) \<inter> (\<Psi>\<^sub>\<phi> `(\<Oplus> (S2))))))" sorry
  then show   "\<ff> = \<Pi>\<^sub>\<phi> ( (\<Z>\<^sub>\<phi>\<^sub>F n ((\<Psi>\<^sub>\<phi> `(\<Oplus> (S1))) \<inter> (\<Psi>\<^sub>\<phi> `(\<Oplus> (S2))))))" using nu6453 by auto
qed
  *)
    
  
  
(*lemma realizationLemmaD :
  fixes S1
  fixes S2
  fixes n
    fixes \<ff>
  assumes "\<And>l . l |\<in>| S1 \<Longrightarrow> closedUnderPlusD (l)"
  assumes "\<And>l . l|\<in>| S2 \<Longrightarrow> closedUnderPlusD (l)"
  assumes "\<And>l . l |\<in>| S1 \<Longrightarrow> l \<noteq> {}"
  assumes "\<And>l . l |\<in>| S2 \<Longrightarrow> l \<noteq> {}"
  defines "\<ff> == \<Pi>\<^sub>\<delta> (fset (\<Z>\<^sub>\<delta> n (( (\<Uplus>\<^sub>\<delta> (S1))) \<inter> ((\<Uplus>\<^sub>\<delta> (S2))))))"
  assumes "\<And> l. (l |\<in>| (S1) \<Longrightarrow> realizedInD l \<ff>)"
  assumes "\<And> l. (l |\<in>| (S2) \<Longrightarrow> realizedInD l \<ff>)"
  shows "\<ff> = \<Pi>\<^sub>\<delta> (fset ( (\<Z>\<^sub>\<delta> n (((\<Oplus>\<^sub>\<delta> (S1))) \<inter> ((\<Oplus>\<^sub>\<delta> (S2)))))))"
  sorry*)
  
  (*
lemma NGreaterZero :
  assumes "(\<And>\<R> i r. r |\<in>| rule_set (\<A> i) \<Longrightarrow> \<L>\<^sub>\<tau>\<^sub>\<rho> (\<A> i) r \<noteq> {})"
  shows "1 \<le> \<N>"
proof (rule ccontr)
  assume "\<not> 1 \<le> \<N>"
  hence n765465 : "\<N> = 0" by arith
      
  from assms existsUniformConstant have n65476 : "realizesUniv \<N>" by auto
  from realizesUniv_def n65476 have "(\<And>i \<alpha> r n2. \<N> < Suc n2 \<longrightarrow> r |\<in>| rule_set (\<A> i) \<longrightarrow> symbol r = \<alpha> \<longrightarrow> realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) r) (\<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> n2 UNIV) \<union> {[]})))" by auto
  hence "(\<And>i \<alpha> r n2. 0 < Suc n2 \<longrightarrow> r |\<in>| rule_set (\<A> i) \<longrightarrow> symbol r = \<alpha> \<longrightarrow> realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) r) (\<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> n2 UNIV) \<union> {[]})))" using n765465 by auto
  hence "(\<And>i \<alpha> r n2.  r |\<in>| rule_set (\<A> i) \<longrightarrow> symbol r = \<alpha> \<longrightarrow> realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) r) (\<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> n2 UNIV) \<union> {[]})))" by auto
  hence "(\<And>i \<alpha> r.  r |\<in>| rule_set (\<A> i) \<longrightarrow> symbol r = \<alpha> \<longrightarrow> realizedInForest (\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i) r) (\<alpha> \<bullet> (\<Pi>\<^sub>\<tau>\<^sub>F (\<Z>\<^sub>\<tau> 0 UNIV) \<union> {[]})))" by auto
      
      obtain  \<alpha> where "( \<alpha> :: abc) =  \<alpha>" by auto
  obtain state where "(state :: stt) = state" by auto
  then obtain stateset where "state |\<in>| stateset" by auto
  then obtain rule where "symbol (rule :: (stt,abc) rule) =  \<alpha>" and "states rule = stateset"        by (meson rule.select_convs(1) rule.select_convs(2)) 
      *)
      
  
  (*proof
 fix x
 assume b1 : "x |\<in>| \<Z>\<^sub>\<tau> n (intersectionLanguageRules (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))"
 from zIntersectLemma b1 have b2 : "x |\<in>| \<Z>\<^sub>\<tau> n UNIV \<and> x \<in> (intersectionLanguageRules (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))" by metis
 from b2 intersectionLanguageRules_def \<A>.simps have b4 : "\<And> i. x \<in> (\<Uplus> ((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> i)) |`| (\<R> i)))" by (metis (full_types) IntE \<A>.cases)
 from b4 have b5 : "\<And> i.   satisfiesApproximatorForRuleSet x (\<R> i) i" sorry
 from \<ff>_def have b3 : "\<ff> n \<R> = \<Z>\<^sub>\<tau> n (\<P> \<R>)" by auto
 from b3 b5 zIntersectLemma show "x |\<in>| (\<ff> n \<R>)" using b2 \<P>_def mem_Collect_eq by blast
qed*)
  
(*lemma gInFD : 
  fixes \<R>
  fixes n
  shows " ( (\<Z>\<^sub>\<delta> n (\<delta>\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (((\<R>) \<aa>\<^sub>1))((((\<R>) \<aa>\<^sub>2)))))) |\<subseteq>| \<Pi> |`| (\<ff> n  \<R>)"
  sorry*)
    
(*        
        
    have n65897 : " tree \<in> (fset (\<Z>\<^sub>\<tau> (Suc n)(\<P> \<R>)))"  using n76465          by (simp add: \<ff>_def fmember.rep_eq)
    hence "height tree \<le> 1" using n7656897  by auto
        
        
    from  n65897 have " tree \<in> (((\<P> \<R>)))" using \<Z>\<^sub>\<tau>_def notin_fset sorry
        
    from singletonPathsMeansSingletonTree have "(\<And>tree path. tree \<in> fset (\<ff> (Suc n)  \<R>) \<Longrightarrow> path |\<in>| \<Pi> tree \<Longrightarrow> path = [\<alpha>])
\<Longrightarrow> (\<And> tree. tree \<in> fset (\<ff> (Suc n)  \<R>) \<Longrightarrow> tree = NODE \<alpha> {||})" by metis
    hence "(\<And> tree. tree \<in> fset (\<ff> (Suc n)  \<R>) \<Longrightarrow> tree = NODE \<alpha> {||})" using n75478 by auto
        
      
        
        
        
        have "tree \<in> (fset (\<Z>\<^sub>\<tau> (1)(\<P> \<R>)))" using n76465          by (simp add: \<ff>_def fmember.rep_eq)
        
        hence "\<And>tree .  tree \<in> (fset (\<Z>\<^sub>\<tau> (Suc n)(\<P> \<R>))) \<Longrightarrow> tree \<in> (fset (\<Z>\<^sub>\<tau> (1)(\<P> \<R>)))"  using \<Z>\<^sub>\<tau>_def restrictionIsFinite2 restrictionIsFinite          by (simp add: inf_fset2.rep_eq) 
         
            
        
            from n656897 have "\<And>tree path . tree \<in> (fset ((\<gg> (Suc n) \<R>))) \<Longrightarrow> (path |\<in>| (\<Pi> tree)) \<Longrightarrow> path = [\<alpha>]" using pathsForTreeLanguage_def by blast
    hence "\<And>tree path . tree \<in> (fset (\<gg> (Suc n)  \<R>)) \<Longrightarrow> (path |\<in>| (\<Pi> tree)) \<Longrightarrow> length path = length [\<alpha>] " by auto
    hence "\<And>tree path . tree \<in> (fset (\<gg> (Suc n)  \<R>)) \<Longrightarrow> (path |\<in>| (\<Pi> tree)) \<Longrightarrow> length path = 1 " by auto
    hence "\<And>tree path . tree \<in> (fset (\<gg> (Suc n)  \<R>)) \<Longrightarrow> (path |\<in>| (\<Pi> tree)) \<Longrightarrow> length path \<le> 1 " by auto
    hence "\<And>tree .  tree \<in> (fset (\<gg> (Suc n)  \<R>)) \<Longrightarrow> height tree \<le> 1" using heightOnlyDependsOnPaths finiteMaxExists  by (metis One_nat_def fimageE le_SucI le_zero_eq) 
    hence n65875 :  "\<And>tree .  tree \<in> (fset (\<Union>| (\<Z>\<^sub>\<phi> (Suc n) (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))))) \<Longrightarrow> height tree \<le> 1"  using \<gg>_def by auto
        
    hence "\<And>tree .  tree \<in> (fset (\<Union>| (\<Z>\<^sub>\<phi> (Suc n) (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))))) \<Longrightarrow> tree \<in> (fset (\<Union>| (\<Z>\<^sub>\<phi> 1 (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2)))))" 
    proof -
      fix tree
      assume "tree \<in> (fset (\<Union>| (\<Z>\<^sub>\<phi> (Suc n) (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2)))))"
      obtain forest where n7646 : "forest |\<in>| \<Z>\<^sub>\<phi> (Suc n) (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))" and n6754656 : "tree |\<in>| forest" using notin_fset ffUnionLemma
        by (metis \<open>tree \<in> fset (\<Union>| (\<Z>\<^sub>\<phi> (Suc n) (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))))\<close>) 
      from n7646 have "\<And>tree . tree |\<in>| forest \<Longrightarrow> tree |\<in>| (\<Union>| (\<Z>\<^sub>\<phi> (Suc n) (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))))" using ffUnionLemma by blast
      hence n65687 : "\<And> tree . tree |\<in>| forest \<Longrightarrow> height tree \<le> 1" using n65875 notin_fset            by fastforce 
      from n7646 \<Z>\<^sub>\<phi>_def   have n6587 :  "forest \<in>  (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))" sorry
      
          
      from n65687 restrictionIsFiniteForests notin_fset have n6587b : "forest |\<in>| boundedForests 1" sorry
      from n6587 n6587b have "forest |\<in>| \<Z>\<^sub>\<phi> 1 (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2))" using \<Z>\<^sub>\<phi>_def by auto 
      hence "tree |\<in>| \<Union>| (\<Z>\<^sub>\<phi> 1 (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2)))" using n6754656 by auto
      then show "tree \<in> (fset (\<Union>| (\<Z>\<^sub>\<phi> 1 (\<Psi>\<^sub>\<Sigma>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2)))))"  using notin_fset by metis
    qed
        
        
      
      
        hence n7546 : "\<And>tree  . tree \<in> (fset (\<ff> (Suc n)  \<R>)) \<Longrightarrow> (\<Pi> tree) |\<subseteq>| (finsert [\<alpha>] fempty)"         by auto 
    hence "(\<Pi> tree) |\<subseteq>| (finsert [\<alpha>] fempty)"  using n76465 notin_fset by metis
    have n7464 : "\<And> children root. (NODE root children) \<in> (fset (\<ff> (Suc n)  \<R>)) \<Longrightarrow> (\<Pi> (NODE root children)) |\<subseteq>| (finsert [\<alpha>] fempty)"      using n7546 by blast 
        
    have "(fset (\<ff> (Suc n)  \<R>)) = {(NODE \<alpha> fempty)}" 
    proof 
      show "fset (\<ff> (Suc n) \<R>) \<subseteq> {NODE \<alpha> {||}}"
      proof 
        fix x
        assume n75687 : " x \<in> fset (\<ff> (Suc n) \<R>)"
        obtain root children where "x = (NODE root children)" using tree.exhaust by auto
        then have n6587 : " (\<Pi> (NODE root children)) |\<subseteq>| (finsert [\<alpha>] fempty)" using n75687  n7464 by auto
        from pathAlternateDef have n54647 : "(\<Pi> (NODE root children)) = (\<lambda> x. (root#x)) |`| (\<Union>| (\<Pi> |`| children) |\<union>| {|[]|})" by auto
        from n6587 have n656587 : "(\<Pi> (NODE root children)) |\<subseteq>| (\<lambda> x. (root#x)) |`| ({|[]|})" by auto
        have n6445877 : "(\<lambda> x. (root#x)) |`| ({|[]|}) = (finsert [root] fempty)" by simp
        hence n76535 : "(finsert [root] fempty) |\<subseteq>| (finsert [\<alpha>] fempty)" using n6587  n656587 by auto
        hence "root = \<alpha>" by auto
        hence " (\<lambda> x. (\<alpha>#x)) |`| (\<Union>| (\<Pi> |`| children) |\<union>| {|[]|}) |\<subseteq>| (finsert [\<alpha>] fempty)" using n76535 n6445877 n54647 n656587 by auto
        hence "(\<Union>| (\<Pi> |`| children) |\<union>| {|[]|}) = {|[]|}" by auto
        
          
        
        
        
        *)
        
  
  
(*
lemma psiSubsetsLemma :
  fixes z
  shows "\<And> p x . (p \<in> (pathsInTree x) \<Longrightarrow> x = psi z \<Longrightarrow> (\<exists>p2.(childrenPathsetsAreSubsets p2 p \<and> p2 \<in> pathsInTree z)))"
proof -
  fix p
  fix x :: "abc tree"
  assume "p \<in> (pathsInTree x)"
  def forest == "(finsert x fempty)"
  def originalForest == "(finsert z fempty)"
    assume " x = psi z"
    hence "forest = psiF originalForest" using forest_def originalForest_def psiF_def sorry
        
    show "(\<exists>p2.(childrenPathsetsAreSubsets p2 p \<and> p2 \<in> pathsInTree z))" sorry
  qed
  *)
    
    
    
    
    (*proof (induct z)
  case (NODE x1a x2a)
  fix p
  fix x
  assume a1 : "(\<And>x2aa p x. x2aa \<in> fset x2a \<Longrightarrow> p \<in> pathsInTree x \<Longrightarrow> x = psi x2aa \<Longrightarrow> \<exists>p2. childrenPathsetsAreSubsets p2 p \<and> p2 \<in> pathsInTree x2aa)"
    assume a2 : "x = psi (NODE x1a x2a)"
  assume a3 : " p \<in> pathsInTree x"
  
    
  from a2  have a10 : "x
      = NODE x1a (fimage (\<lambda> symbol2 .
                              psi (NODE symbol2 (\<Union>| (fimage childrenSet (childrenWithSymbol symbol2 x2a)))
                                  )
                              )
                              (fimage root x2a)
                     )"
    by (metis psi.simps)
      from a3 have a11 : "(isAPathp p) \<and> (( \<exists>e1.\<exists>tail.(p = (e1#tail) \<and> (isNodeIn e1 x) \<and> (isRootNode e1)        )      ))"
        by (simp add: pathsInTree_def)
    (* also here, for induction should not take isAPathp but instead something that doesn't check whether the first element is a root *)
      obtain child where q1 : "child |\<in>| x2a" and "(tl p) \<in>  pathsInTree child" sorry
      define childRoot where q2 : "childRoot = (root child)"
        define psiChild where q3 : "psiChild = psi (NODE childRoot (\<Union>| (fimage childrenSet (childrenWithSymbol childRoot x2a))))"
        from a10 q1 q2 q3 have "psiChild  |\<in>| (childrenSet x)" by (metis (no_types, lifting) childrenSet.simps fimage_eqI)
            
            
      obtain p2 :: "abc node list" where "childrenPathsetsAreSubsets p2 p \<and> p2 \<in> pathsInTree psiChild" sorry
          
          
      obtain newNode :: "abc node" where "down newNode = (z :: abc tree)" sorry (* TODO redefine node so that context is not used anymore. not really useful, since context is never used. "node = a tree" is totally adequate *)
      define newPath where q4 : "newPath = newNode#p2"
        
      from a11  have "down (hd p) = x" using isNodeIn_def isRootNode_def by force 
      have "labelOfNode newNode = x1a" sorry
      from a11 have "x1a = labelOfNode (hd p)  " sorry
      have "\<Pi> z |\<subseteq>| \<Pi> x" sorry
      then have "(\<Pi> (down newNode) |\<subseteq>| \<Pi> (down (hd p)))" by (simp add: \<open>down (hd p) = x\<close> \<open>down newNode = z\<close>)
  then show ?case sorry
qed
   
   
proof -
{ (* do induction along the height of z *)
fix x1a x2a p x
assume b7 : "x = psi (NODE (x1a :: abc) x2a)"
assume b10 : "(\<And> x2aa p x. height x2aa < height (NODE x1a x2a)  \<Longrightarrow> p \<in> pathsInTree x \<Longrightarrow> x = psi x2aa \<Longrightarrow> \<exists>p2. childrenPathsetsAreSubsets p2 p \<and> p2 \<in> pathsInTree x2aa)"
assume b2 : "(p :: abc node list) \<in> pathsInTree x"


from b2 pathsInTree_def obtain e1 tail where b3 : "(isAPathp p)" and b4 : " p = (e1#tail)" and b5 : "isNodeIn e1 x" and b6 : "(isRootNode e1)" by blast
def head == "(| up = PLACEHOLDER, down = (NODE x1a x2a) |)"
have "\<exists>p2. childrenPathsetsAreSubsets p2 p \<and> p2 \<in> pathsInTree (NODE x1a x2a)" proof (rule disjE)
show "tail = [] \<or> tail \<noteq> []" by blast
{ assume c3 : "tail=[]"
  def p2 == "head#[]"
  show "\<exists>p2. (childrenPathsetsAreSubsets p2 p \<and> p2 \<in> pathsInTree (NODE x1a x2a))" sorry
  }
{ assume c3 : "tail \<noteq> []"
  
  from b7 have "x = NODE x1a (fimage (\<lambda> symbol2 .
                              psi (NODE symbol2 (\<Union>| (fimage childrenSet (childrenWithSymbol symbol2 x2a)))
                                  )
                              )
                              (fimage root x2a)
                     )" by (metis fimage_cong psi.simps) 
  from c3 obtain tailHead tailTail where c4 : "tail = tailHead#tailTail" using list.exhaust by blast
  
  obtain symbol where "(childrenWithSymbol symbol x2a) \<noteq> fempty" sorry
  def symbolTree == "(NODE symbol (\<Union>| (fimage childrenSet (childrenWithSymbol symbol x2a))))"
  from b2 c4 obtain symbol :: "abc" where c5 : "tail \<in> pathsInTree ( psi symbolTree)" sorry
  have c6 : "height symbolTree < height (NODE x1a x2a)" sorry
  from c5 c6 b10 obtain p2Down where c11 : "childrenPathsetsAreSubsets p2Down tail \<and> p2Down \<in> pathsInTree symbolTree" by blast
  obtain childInSymbolTree where c12 : "childInSymbolTree |\<in>| (childrenWithSymbol symbol x2a)" and c13 : "p2Down \<in> pathsInTree childInSymbolTree" sorry
  from c12 have "childInSymbolTree |\<in>| x2a" sorry
  def p2 == "head#p2Down"
  have "(childrenPathsetsAreSubsets p2 p)" sorry
  have "(p2 \<in> pathsInTree (NODE x1a x2a))" sorry
  show "\<exists>p2. (childrenPathsetsAreSubsets p2 p \<and> p2 \<in> pathsInTree (NODE x1a x2a))" sorry
  }

qed
}
show "\<And> p x. p \<in> pathsInTree x \<Longrightarrow> x = psi z \<Longrightarrow> \<exists>p2. childrenPathsetsAreSubsets p2 p \<and> p2 \<in> pathsInTree z " sorry
qed
  *)
    
      
          
          
      (*
   
  have c3 : "\<And> \<ii> x p . p \<in> (pathsInTree x) \<Longrightarrow> x|\<in>| y \<Longrightarrow>  (( (\<exists> r  . (hd r |\<in>| (\<R> \<ii>)) \<and> (pathFitsListAndListIsARun \<ii> p r))  ))" 
  proof -
    fix  \<ii>  p
    fix x :: "abc tree"
      (*
    from c10 obtain forest where "y = \<Psi>\<^sub>\<phi> forest" and "forest \<in> ((\<Union>| ( ((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>)) |`| (((\<R>) \<ii>))))))" by auto
        *)
    assume n76988 : "p \<in> (pathsInTree x)"
    assume "x|\<in>| y"
    from psiSubsetsLemma n76988 have "\<And> p x z . p \<in> pathsInTree x \<Longrightarrow> x = psi z \<Longrightarrow> \<exists>p2. (childrenPathsetsAreSubsets p2 p \<and> p2 \<in> pathsInTree z)" by auto
    then have n8798 : "\<And>  z .  x = psi z \<Longrightarrow> \<exists>p2. childrenPathsetsAreSubsets p2 p \<and> p2 \<in> pathsInTree z" using n76988 by auto
        
        
      obtain forest where n6567 : "{|x|} = psiF forest" and "forest \<in> ((\<Uplus> ( ((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>)) |`| (((\<R>) \<ii>))))))" sorry
          
   (*   from n8798 n6567 obtain p2 where "childrenPathsetsAreSubsets p2 p" and "p2 \<in> pathsInTree tree" by auto*)
          
      
    show "\<exists>r. hd r |\<in>| \<R> \<ii> \<and> pathFitsListAndListIsARun \<ii> p r " sorry
  qed
    
    
   
    
    (*
  from c10 have c3 : "\<And> \<ii> x p . p \<in> (pathsInTree x) \<Longrightarrow> x|\<in>| y \<Longrightarrow>  ((\<exists> forest . (y = \<Psi>\<^sub>\<phi> forest \<and> forest \<in> ((\<Uplus> ( ((\<L>\<^sub>\<phi>\<^sub>\<rho> (\<A> \<ii>)) |`| (((\<R>) \<ii>)))))))))" using psiSubsetsLemma *)
    
    
  from c3 pathSatisfiesApproximatorForRuleSet_def have c2 : "\<And> \<ii> x p . p \<in> (pathsInTree x) \<Longrightarrow> x|\<in>| y \<Longrightarrow>  pathSatisfiesApproximatorForRuleSet p (\<R> \<ii>) \<ii>" by metis
  from satisfiesApproximatorForRuleSet_def c2 have c1 : "\<And> \<ii> x. x |\<in>| y \<Longrightarrow> satisfiesApproximatorForRuleSet x (\<R> \<ii>) \<ii>" by metis
  from c1 b1 \<P>_def have c11 : "x \<in> (\<P> \<R>)" by auto
  from c11 b3 b1 \<ff>_def heightForestBounded_def \<Z>\<^sub>\<tau>_def show "x |\<in>| (\<ff> n \<R>)" by (simp add: finterI restrictionIsFinite2) 
qed
  *)

                (*
                
                
            from pathFitsListAndListIsARun.simps n5466897 n544877 obtain head tail where n64r77 : "r = head#tail"                      by (metis hd_Cons_tl) 
            from pathFitsListAndListIsARun.simps(2) n5466897 n64r77 n6577988 have n53467 : "labelOfNode pathHead = symbol head" by auto
            from n6577988   n654e53 pathsInTree_def have "down pathHead = x" by fastforce
            hence "labelOfNode pathHead = root x" using   labelOfNode_def  by auto
            hence "labelOfNode pathHead = \<alpha>" using n645787 by auto
            hence "symbol head = \<alpha>" using n53467 by auto
            then show "\<alpha> |\<in>| fimage symbol (\<R> \<ii>)" using n53456877          using n64r77 by auto *)
                
                  (*
                  
          obtain path where n654e53 : "path \<in> pathsInTree x"            using theSingletonPathExists by auto 
          hence n544877 : "path \<noteq> []" using pathsInTree_def                   by blast 
          from satisfiesApproximatorForRuleSet_def n654e53 n6576 have n5466 : "\<And> \<ii>. pathSatisfiesApproximatorForRuleSet path  (\<R> \<ii>) \<ii>" by auto*)
              (*
              
              
              
          have "\<And>\<ii> . \<alpha> |\<in>| fimage symbol (\<R> \<ii>)"
          proof -
            fix \<ii>
            from pathSatisfiesApproximatorForRuleSet_def n5466 obtain r where n53456877 : " hd r |\<in>| (\<R> \<ii>)" and n5466897 : " pathFitsListAndListIsARun \<ii> path r" by blast
            from n544877 obtain pathHead pathTail where n6577988 : "path = pathHead#pathTail"                      by (metis hd_Cons_tl) 
            from pathFitsListAndListIsARun.simps n5466897 n544877 obtain head tail where n64r77 : "r = head#tail"                      by (metis hd_Cons_tl) 
            from pathFitsListAndListIsARun.simps(2) n5466897 n64r77 n6577988 have n53467 : "labelOfNode pathHead = symbol head" by auto
            from n6577988   n654e53 pathsInTree_def have "down pathHead = x" by fastforce
            hence "labelOfNode pathHead = root x" using   labelOfNode_def  by auto
            hence "labelOfNode pathHead = \<alpha>" using n645787 by auto
            hence "symbol head = \<alpha>" using n53467 by auto
            then show "\<alpha> |\<in>| fimage symbol (\<R> \<ii>)" using n53456877          using n64r77 by auto 
          qed
            
        qed
          
            
(*            hence "\<alpha> |\<in>| (fimage symbol (\<R> \<aa>\<^sub>1) |\<union>| fimage symbol (\<R> \<aa>\<^sub>2))" by auto*)
                
                
            have "fset (\<ff> (Suc n)  (rulesPerAlpha \<alpha>)) \<noteq> {}" sorry 
                
                (* have u1 : "\<And> \<alpha> . \<alpha> |\<in>| occurringAlphas \<Longrightarrow> (\<Pi>\<^sub>\<tau>\<^sub>F ((\<ff> (Suc n)  (rulesPerAlpha \<alpha>)))) = \<Pi>\<^sub>\<tau>\<^sub>F ((gAlpha \<alpha>))" *)
                
            show "False" sorry
          qed*)