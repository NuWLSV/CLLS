# !/bin/bash

SEND_THREAD_NUM=128 # 线程数（需要设置）

res_dir="/pub/data/wangxy_s/output/max_sample_30_seed" #结果存放的文件夹（需要设置）
instance_dir="/pub/data/wangxy_s/wecnf" #例子存放的文件夹（需要设置）
solver_dir="/pub/data/wangxy_s/linear_nuwlsv/NuWLS-main/NuWLS-source-code/nuwls-we"
time_limit=300
classes=(uw w)
years=(2021 2022 2023) 
SEED=1

# export OMP_PROC_BIND=spread
# export OMP_PLACES="{0:16}, {16:16}, {32:16}, {48:16}, {64:16}, {80:16}, {96:16}, {112:16}, {128:16}, {144:16}, {160:16}, {176:16}, {192:16}, {208:16}, {224:16}, {240:16}"

tmp_fifofile="/tmp/$$.fifo" # 脚本运行的当前进程ID号作为文件名
mkfifo "$tmp_fifofile" # 新建一个随机fifo管道文件
exec 6<>"$tmp_fifofile" # 定义文件描述符6指向这个fifo管道文件
rm $tmp_fifofile
for i in $(seq 1 $SEND_THREAD_NUM)
do
    echo # for循环 往 fifo管道文件中写入 $SEND_THREAD_NUM 个空行
done >&6

#####################################################
eNums=(1 2 3 4 5) #随机种子，此处会用10个随机种子都执行一遍
# ulimit -t 1800 #设置的最大时间限制
# ulimit -s unlimited #设置的最大内存限制 400G
# ulimit -n 65535
# ulimit -u 81920

# rm ./nuwls-we
# make

# rm /pub/data/wangxy_s/output/warnings/*
res_base=$res_dir

for SEED in ${eNums[@]}
do
	res_dir=$res_base$SEED
	if [ -d $res_dir ];then 
		rm -r $res_dir
	fi
	if ! [ -d $res_dir ];then 
		mkdir $res_dir
	fi
	for class in ${classes[@]}
	do
		if ! [ -d $res_dir/$class ];then 
			mkdir $res_dir/$class
		fi
		for year in ${years[@]}
		do
			if [ ! -d $res_dir/$class/$year ];then 
				mkdir $res_dir/$class/$year
			fi
			res_solver_ins=$res_dir/$class/$year
			instance=$instance_dir/$class/$year
			rm $res_solver_ins/*

			for dir_file in $instance/*
			do
				file=$(basename $dir_file)
				echo $file
				touch $res_solver_ins/$file # 创建一个空文件
				read -u 6
				{
					timeout $time_limit $solver_dir $dir_file $SEED  # smt.random_seed=${eNums[$i]} -t:1210000  #执行的命令（需要设置）
					echo >&6
				} >> $res_solver_ins/$file   & #结果和时间的输出
			done
		done
	done
done
#for ((i=0;i<${#eNums[*]};i++))
#do2>>/pub/data/wangxy_s/output/warnings/$file
# 	res_solver_ins=$res_dir
# 	instance=$instance_dir
# 	for dir_file in $instance/*
# 	do
# 		file=$(basename $dir_file)
# 		echo $file
# 		touch $res_solver_ins/$file # 创建一个空文件
# 		read -u 6
# 		{
# 			time /pub/data/wangxy_s/Parallel-NuWLS/starexec_nuwls-we-with-runsolver.sh $dir_file 1 100 $res_solver_ins/$file # smt.random_seed=${eNums[$i]} -t:1210000  #执行的命令（需要设置）
# 			echo >&6
# 		} 2>>$res_solver_ins/$file  & #结果和时间的输出 
# 	done
# #done

exit 0
