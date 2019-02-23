#!/bin/bash

# 使い方
# ./run_test.sh

results_dir="results"
mkdir -p $results_dir

total=0
correct=0

# Compile coqlib.v
coqc coqlib.v

echo "gold_answer/system_answer"

for f in ./testset/*.ccg; do
  let total++
  fname=${f##*/}
  # ./parsing.sh $f
  ./parsing.sh $f > $results_dir/${fname/.ccg/.answer}
  sys=`cat ${results_dir}/${fname/.ccg/.answer}`
  gold=`cat testset/${fname/.ccg/.answer}`
  if [ "${sys}" == "${gold}" ]; then
    let correct++
  fi  
  echo "${fname}: ${gold}/${sys}"
done

accuracy=`echo "scale=4; $correct / $total" | bc -l`
echo "Accuracy: "$correct" / "$total" = "$accuracy

echo "<!doctype html>
<html lang='en'>
<head>
  <meta charset='UTF-8'>
  <title>Evaluation results</title>
  <style>
    body {
      font-size: 1.5em;
    }
  </style>
</head>
<body>
<table border='1'>
<li>Accuracy : "$correct" / "$total" = "$accuracy"</li>
<tr>
  <td>id</td>
  <td>problem</td>
  <td>gold answer</td>
  <td>system answer</td>
</tr>" > $results_dir/main.html

red_color="rgb(255,0,0)"
green_color="rgb(0,255,0)"
white_color="rgb(255,255,255)"
gray_color="rgb(136,136,136)"

for gold_filename in `ls -v ./testset/*.answer`; do
  fname=${gold_filename##*/}
  sentences=`python get_sentences.py ./testset/${fname/.answer/.ccg} | sed 's|#END#|<br>|g'`
  system_answer=`cat $results_dir/${fname/.ccg/.answer} | awk -F',' '{print $1}'`
  gold_answer=`cat $gold_filename`
  echo '<tr>
  <td>'${fname/.answer/}'</td>
  <td>'$sentences'</td>
  <td>'${gold_answer}'</td>' >> $results_dir/main.html
  color=$white_color
  if [ "$gold_answer" == "yes" ] || [ "$gold_answer" == "no" ]; then
    if [ "$gold_answer" == "$system_answer" ]; then
      color=$green_color
    else
      color=$red_color
    fi
  elif [ "$system_answer" == "yes" ] || [ "$system_answer" == "no" ]; then
    color=$red_color
  else
    color=$white_color
  fi
  echo '<td><a style="background-color:'$color';" href="'${fname/.answer/.html}'">'$system_answer'</a></td>' >> $results_dir/main.html
done
