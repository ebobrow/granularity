theory Isa imports Main begin

theorem comm: "B \<and> A \<longrightarrow> A \<and> B"
apply(rule impI)