#!/bin/bash

ccg=$1

home=$HOME
c2l_dir="${home}/ccg2lambda"
semantics="semantic_lexicon_for_question.yaml"
file=${ccg##*/}
jigg=${file/.ccg/.xml}

res_dir="results"
mkdir -p $res_dir

python $c2l_dir/scripts/ccg2jiggxml.py -i $ccg > $res_dir/$jigg

python ${c2l_dir}/scripts/semparse.py $res_dir/$jigg $semantics $res_dir/${jigg/.xml/.sem.xml} \
    2> $res_dir/${jigg/.xml/.sem.err}

python ${c2l_dir}/scripts/visualize.py $res_dir/${jigg/.xml/.sem.xml} \
    --format vertical \
    > $res_dir/${jigg/.xml/.html}

# python callprover9.py $res_dir/${jigg/.xml/.sem.xml}

