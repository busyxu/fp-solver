all_dicts=$(ls -d */)
for dict in $all_dicts
do
  #work_dic=$(echo ${dict%%/})
  cd ${dict}
  echo ${dict}" "$(find . -name '*.c' | wc -l)
  result_dicts=$(ls -d */)
  for rdict in ${result_dicts}
  do
    echo ${rdict}
  done
  cd ..
done


#all_dicts=`ls -d */`
#for dict in $all_dicts:
#do
#  #work_dic=$(echo ${dict%%/})
#  cd ${dict}
#  echo ${dict}"  "`find . -name "*.c" | wc -l`
#  result_dicts=`ls -d */`
#  for rdict in ${result_dicts}:
#  do
#    echo ${rdict}"=========="
#  done
#  cd ..
#done


