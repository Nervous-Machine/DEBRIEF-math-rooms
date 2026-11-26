#!/bin/sh
# usage: rescore.sh REPO_DIR — rescores every arm of builds 1–3 with its own root, challenge, blueprint and predictions; arms without a blueprint are scored with none, so no node comparison is made
cd "$1" || exit 1
A1="--root erdos_766.variants.dirac_erdos --ns Erdos766 --challenge rooms/Challenge.lean --blueprint blueprint_nodes.yaml --predictions blueprint_predictions.yaml --control results/control_Erdos766_Solution.lean"
A2="--root consecutive_exponents --ns Panda2608 --challenge rooms/Challenge_2608.lean --blueprint blueprint_2608_nodes.yaml --predictions blueprint_2608_predictions.yaml"
A159="--root erdos_159 --ns Erdos159 --challenge rooms/Challenge_159.lean --blueprint blueprint_159_nodes.yaml --predictions blueprint_159_predictions.yaml"
A569="--root cambie_freschi --ns Erdos569 --challenge rooms/Challenge_569.lean --blueprint blueprint_569_nodes.yaml --predictions blueprint_569_predictions.yaml"
run() { python3 rooms/score.py . "$1" --tokens "$2" $3 >/dev/null 2>&1 || echo "FAILED $1"; }
run R1_full 99114 "$A1"; run R2_binary 151407 "$A1"; run R3_none 165568 "$A1"; run R1_noplan 93763 "${A1% --blueprint*} --blueprint none --predictions blueprint_predictions.yaml --control results/control_Erdos766_Solution.lean"
run B2_A_full 176408 "$A2"; run B2_B_full_noplan 176823 "--root consecutive_exponents --ns Panda2608 --challenge rooms/Challenge_2608.lean --blueprint none --predictions blueprint_2608_predictions.yaml"; run B2_C_binary 266879 "$A2"; run B2_D_none 250342 "$A2"
run B3_159_H_full_hold 205979 "$A159"; run B3_159_H_none_hold 321858 "$A159"; run B3_159_H_none_plain 268787 "$A159"
run B3_569_A_full_hold 349230 "$A569"; run B3_569_B_full_noplan_hold 191580 "--root cambie_freschi --ns Erdos569 --challenge rooms/Challenge_569.lean --blueprint none --predictions blueprint_569_predictions.yaml"
