theory Game_Theory 
  imports "HOL-Probability.Probability_Mass_Function"
begin

section "Defining a Simultaneous Move Game"

locale strategic_game = 
  fixes pure_strategies :: "'player :: finite  \<Rightarrow> 'strategy set"
    and payoffs :: "'strategy^'player \<Rightarrow> ('payoff :: linorder)^'player"
assumes players_can_play: "pure_strategies i \<noteq> {}"
begin

corollary players_have_a_move: "\<exists>s. s\<in>pure_strategies i"
  using players_can_play by auto 

text "Strategy selection" 
definition pure_profile :: "('strategy^'player) \<Rightarrow> bool"
  where "pure_profile s = (\<forall>i. s$i \<in> pure_strategies i)"

definition payoff :: "'strategy^'player \<Rightarrow> 'player \<Rightarrow> 'payoff" 
  where "payoff s i = (payoffs s)$i"

text "We prove the existence of legal plays, represented as vectors of legal strategies.
In particular, legal plays exist that include any particular choice of strategy for any player."

lemma pure_profile_fix_exists: 
  fixes s\<^sub>i :: "'strategy" 
    and i :: 'player
  assumes fixed_strategy:  "s\<^sub>i \<in> pure_strategies i" 
  shows "\<exists>s. pure_profile s \<and> s$i = s\<^sub>i" 
proof -
  let ?s = "(\<chi> j. if j = i then s\<^sub>i else (SOME s\<^sub>j. s\<^sub>j \<in> pure_strategies j))"
  have "\<forall>j. ?s$j \<in> pure_strategies j"
    by (simp add: fixed_strategy players_can_play some_in_eq)
  hence "pure_profile ?s"
    by (simp add: pure_profile_def)

  moreover have "?s$i = s\<^sub>i"
    by simp 

  ultimately show ?thesis
    by auto
qed

lemma pure_profile_exists: "\<exists>s. pure_profile s" 
  using pure_profile_fix_exists players_have_a_move by blast 

text "If n denotes the number of players, we represent the (n-1)-dimensional vector of strategies
chosen by players other than player i as a function from strategies (which player i may choose) to
(n-dimensional) strategy vectors."

definition pure_profile_completion :: "'strategy \<Rightarrow> 'strategy^'player \<Rightarrow> 'player \<Rightarrow> 'strategy^'player"
  where "pure_profile_completion s\<^sub>i s i = (\<chi> j. if j = i then s\<^sub>i else s$j)"

notation pure_profile_completion ("(_,_\<^sub>-\<^sub>_)" [80, 80] 80)

lemma player_chooses_completion: "(s\<^sub>i,s\<^sub>-\<^sub>i)$i = s\<^sub>i"
  by (simp add: pure_profile_completion_def)

lemma pure_completion_fixes_other_players: 
  fixes i :: 'player
    and j :: 'player
  assumes "i \<noteq> j"
  shows "(s\<^sub>i,s\<^sub>-\<^sub>i)$j = s$j"
  using assms pure_profile_completion_def by auto

lemma pure_completion_legal_iff: 
  fixes i :: 'player 
    and s :: "'strategy^'player"
  shows "(pure_profile (s\<^sub>i,s\<^sub>-\<^sub>i)) = ((s\<^sub>i \<in> pure_strategies i) \<and> 
        (\<forall>j. ((j \<noteq> i) \<longrightarrow> s$j \<in> pure_strategies j)))"
proof - 
  have "(pure_profile (s\<^sub>i,s\<^sub>-\<^sub>i)) = (\<forall>j. (s\<^sub>i,s\<^sub>-\<^sub>i)$j \<in> pure_strategies j)"
    by (simp add: pure_profile_def)
  hence "(pure_profile (s\<^sub>i,s\<^sub>-\<^sub>i)) = (((s\<^sub>i,s\<^sub>-\<^sub>i)$i \<in> pure_strategies i) \<and>
         (\<forall>j. ((j \<noteq> i) \<longrightarrow> (s\<^sub>i,s\<^sub>-\<^sub>i)$j \<in> pure_strategies j)))"
    by auto
  thus ?thesis
    by (simp add: player_chooses_completion pure_completion_fixes_other_players)
qed

lemma pure_completion_of_legal_play: 
    fixes s :: "'strategy^'player"
  assumes legal_play: "pure_profile s"
    shows "pure_profile (s\<^sub>i,s\<^sub>-\<^sub>i) = (s\<^sub>i \<in> pure_strategies i)"
  using pure_completion_legal_iff legal_play pure_profile_def by auto

lemma reconstruct_pure_profile [simp]: 
  fixes s :: "'strategy^'player"
    and i :: 'player 
  shows "(s$i,s\<^sub>-\<^sub>i) = s" 
proof - 
  have "\<forall>j. (s$i,s\<^sub>-\<^sub>i)$j = s$j"
    using pure_completion_fixes_other_players player_chooses_completion by metis 
  thus ?thesis
    by (simp add: vec_eq_iff) 
qed

subsection "Basic solution concepts"

(* Note that ((s')$i,s'\<^sub>-\<^sub>i) is just s', which simp knows due to reconstruct_pure_profile. *)
definition dominant_strategy_solution :: "'strategy^'player \<Rightarrow> bool"
  where "dominant_strategy_solution s = ((pure_profile s) \<and> 
        (\<forall>i. \<forall>s'. (pure_profile s' \<longrightarrow> payoff (s$i,s'\<^sub>-\<^sub>i) i \<ge> payoff (s'$i,s'\<^sub>-\<^sub>i) i)))"

definition pure_nash_equilibrium :: "'strategy^'player \<Rightarrow> bool"
  where "pure_nash_equilibrium s = ((pure_profile s) \<and> 
        (\<forall>i. \<forall>s'\<^sub>i \<in> pure_strategies i. payoff (s$i,s\<^sub>-\<^sub>i) i \<ge> payoff (s'\<^sub>i,s\<^sub>-\<^sub>i) i))"

lemma completion_reverses_itself: "(a,(b,s\<^sub>-\<^sub>i)\<^sub>-\<^sub>i) = (a,s\<^sub>-\<^sub>i)"
proof - 
  have "\<forall>j. (a,(b,s\<^sub>-\<^sub>i)\<^sub>-\<^sub>i)$j = (a,s\<^sub>-\<^sub>i)$j"
    by (metis player_chooses_completion pure_completion_fixes_other_players)
  thus ?thesis
    by (simp add: vec_eq_iff) 
qed

text "Dominant pure strategy solutions are pure Nash equilibria."
lemma dominant_imp_pure_nash:
  fixes s
  assumes dom: "dominant_strategy_solution s"
  shows "pure_nash_equilibrium s"
proof - 
  have "pure_profile s"
    using dom dominant_strategy_solution_def by auto
  
  moreover have "\<forall>i. \<forall>s'. (pure_profile s' \<longrightarrow> payoff (s$i,s'\<^sub>-\<^sub>i) i \<ge> payoff s' i)"
    using dom dominant_strategy_solution_def by auto
  hence "\<forall>i. \<forall>s'\<^sub>i \<in> pure_strategies i. (pure_profile (s'\<^sub>i,s\<^sub>-\<^sub>i) \<longrightarrow> 
        payoff (s$i,(s'\<^sub>i,s\<^sub>-\<^sub>i)\<^sub>-\<^sub>i) i \<ge> payoff (s'\<^sub>i,s\<^sub>-\<^sub>i) i)"
    by simp
  hence "\<forall>i. \<forall>s'\<^sub>i \<in> pure_strategies i. (pure_profile (s'\<^sub>i,s\<^sub>-\<^sub>i) \<longrightarrow> 
        payoff s i \<ge> payoff (s'\<^sub>i,s\<^sub>-\<^sub>i) i)"
    by (simp add: completion_reverses_itself)
  hence "\<forall>i. \<forall>s'\<^sub>i \<in> pure_strategies i. (pure_profile s \<longrightarrow> 
        payoff s i \<ge> payoff (s'\<^sub>i,s\<^sub>-\<^sub>i) i)"
    using pure_completion_of_legal_play by simp 

  ultimately show ?thesis
    using pure_nash_equilibrium_def by auto 
qed

end

text "Strategic form games with real-valued payoffs."
locale real_out_strategic_game = strategic_game pure_strategies payoffs
  for payoffs :: "('strategy, 'player) vec \<Rightarrow> (real, 'player :: finite) vec"
  and pure_strategies
begin

text "For real-valued payoffs, costs can be defined to be their additive inverse."
definition costs :: "('strategy, 'player) vec \<Rightarrow> (real, 'player) vec"
  where "costs s = -payoffs s"

definition cost :: "('strategy, 'player) vec \<Rightarrow> 'player \<Rightarrow> real"
  where "cost s i = (costs s)$i"

lemma cost_neg_pay: 
  shows "cost s i = -payoff s i"
  by (simp add: cost_def costs_def payoff_def)

end

end