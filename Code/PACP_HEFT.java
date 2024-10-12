package cloud.workflowScheduling.methods.opt_makespan;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Random;

import cloud.workflowScheduling.methods.opt_makespan.AILS.copy_sol;
import cloud.workflowScheduling.setting.Allocation;
import cloud.workflowScheduling.setting.Edge;
import cloud.workflowScheduling.setting.Scheduler;
import cloud.workflowScheduling.setting.Solution;
import cloud.workflowScheduling.setting.Task;
import cloud.workflowScheduling.setting.VM;
import cloud.workflowScheduling.setting.Workflow;


public class PACP_HEFT implements Scheduler{
	
	
	//测试策略开关
	private final int limit_iter = 10^7; //限制迭代次数,设置为无穷大则等价于原始GRP_HEFT 10^7
	public boolean is_ban_CAT1 = false;
	public boolean is_ban_CAT2 = false;
	public boolean is_ban_enhance = false;
	
	
	
	private boolean is_print_information = false; //是否打印过程信息 true or false

	//随机种子
	private Random rand = new Random();
	//问题相关变量
	private final double tiny_num = 1E-10; //极小正数
	Workflow wf = null; //调度工作流
	private double budget; //预设预算
	private int task_num;//wf中包含的任务个数
	private Task TaskArray[] = null;//所有任务按照id存放到TaskArray中
	private long TransDataSize[][];//TransDataSize[i][j]存储任务i传递给任务j的数据量
	private ArrayList<ArrayList<Integer>> parent_tasks_id;//存放每个任务所有前置任务的id
	private ArrayList<ArrayList<Integer>> child_tasks_id;//存放每个任务所有后继任务的id
	private boolean is_child[][]; //is_child[i][j]表示任务j是否是任务i的子任务
	private int entry_task_id; //Workflow中entry task被创建时的internalId
	private int exit_task_id;   //Workflow中end task被创建时的internalId
	private double TransRequireTime[][];//TransRequireTime[i][j]存储任务i传递给任务j的数据所需时间
	private boolean can_arrive[][];  //can_arrive[i][j] 表示任务i是否可在有向无环图到达j
	private int arrive_tasks[][]; //arrive_tasks[i][0]表示任务i可达的任务个数，后续罗列各个任务
	private int pass_tasks[][]; //pass_tasks[i][0]表示可达任务i(到达任务i可经过)的任务个数，后续罗列各个任务
	private int vm_types_speed_descend[];  //将使用的机器类型按照速度降序排列
	private int vm_types_ucost_descend[];  //将使用的机器类型按照单位时段价格降序排列
	private int vm_types_overall_descend[];//将使用的机器类型按照性价比(速度/单位时段价格)降序排列
	private int vm_type_speed_rank[]; //每个机器类型的速度排名(未使用机器类型排名为机器类型数+1)
	private int vm_type_ucost_rank[]; //每个机器类型的时价排名(未使用机器类型排名为机器类型数+1)
	private int vm_type_overall_rank[];//每个机器类型的性价比排名(未使用机器类型排名为机器类型数+1)
	private int task_level_from_exit[];  //每个任务的反向深度,end_task记为0
	private int task_level_from_entry[];  //每个任务的正向深度,entry_task记为0
	//private int workflowDepth; //WLA使用,入口任务的depth
	//private int tasks_of_exit_level[][];  //tasks_of_exit_level[i][0]表示task_level_from_exit值为i的个数,后续开始罗列各个任务
	//private int tasks_of_entry_level[][]; //tasks_of_entry_level[i][0]表示task_level_from_entry值为i的个数,后续开始罗列各个任务
	//private double predicted_et[]; //每个任务预计执行时间
	//private double predicted_speed; //预计的平均处理速度
	private double max_input_time[]; //各个任务所有入边最大传输时间
	private double max_output_time[];//各个任务所有出边最大传输时间
	
	//解相关变量
	private double cost = 0.0; //完成调度后,实际使用的budget
	private double makespan = Double.MAX_VALUE; //完成调度时间
	private boolean feasiblity = false;
	private VM  VM_Array[]; //所有被使用的机器按照其id存放在VM_Array中
	private int Vm_of_task[]; //每个任务被分配的机器
	private int Tasks_of_vm[][]; //每个vm执行的所有task,Tasks_of_vm[i][0]表示使用第i个机器的任务数，Tasks_of_vm[i][1]开始按照start_time由小到大罗列任务
	private int execute_rank_on_its_vm[];//每个任务在其占用机器上是第几个被执行的任务，也就是该任务在Tasks_of_vm的列号
	private int used_vm_num = 0; //使用的vm个数,即正在被占用的VM机器数目
	private double start_time[] ; //start_time[i]表示第i个任务的开始时间
	private double finish_time[] = null; //finish_time[i]表示第i个任务的完成时间
	private double execute_time[]; //执行时间, execute_time[i] = finish_time[i] - start_time[i]
	
	private ArrayList<Integer> leased_VM_types = null; //租用机器的全部类型,按照性价比从前往后排序
	private int[] available_VM_hour = null;   //各个租用机器类型的个数(每个机器租用1个计费时段)
	private double avg_speed = 0.0; //所有租赁机器的平均处理速度
	private double accumulate_time[] = null;
	ArrayList<Integer> task_sort_list = null; //处理任务顺序
	
	
	//最优解信息
	copy_sol best_solution = null;

	
	
	@Override
	public Solution schedule(Workflow wf) {
		set_rand_seed(wf.seed); //added by fan, fix random seed to analysis
		//构建问题模型,去除被支配机器类型
		Build_problem_condiction(wf);
		//构建算法环境，初始化相关变量
		Build_alg_condiction();
		
		//写循环
		//boolean is_update_best = false; //is_recal_accumulate_time策略变量
		int CAT_model = 0;
		
		int start_index = 0; //每轮迭代只考虑vm_types_overall_descend[start_index]以及后面的机器类型
		copy_sol best_copy = new copy_sol();
		while(start_index<vm_types_overall_descend.length) {
			//清空当前解
			clear_solution();
			//选机器，选取结果存放至this.leased_VM_types,this.leased_VM_num
			lease_VM(start_index);
			
			if(is_ban_CAT1==true && CAT_model==1) {
				CAT_model=2;
			}
			//新阶段开始则清空且备份最优解
			if(CAT_model==0) {
				best_copy.copy_inf(best_solution); //备份最优解到best_copy
				best_solution = new copy_sol(); //清空最优，用于收集本轮机器的最优解
			}
			
			//System.out.println("CAT_model = "+CAT_model);
			
			//任务排序
			if(CAT_model==0) cal_accumulate_time();
			else if(CAT_model==1) recal_accumulate_time();
			else if(CAT_model==2) rerecal_accumulate_time();
			else {
				System.out.println("line111: CAT_model ERROR,CAT_model = "+CAT_model);
				while(true) {;}
			}
			
			
			task_sort_list = desc_sort_tasks(this.accumulate_time);
			//给任务分配机器
			assign_vm(task_sort_list);
			//计算cost
			this.cost = total_cost();
			//计算makespan
			this.makespan = total_maskspan();
			//计算可行性
			if(this.cost>=this.budget+tiny_num) {
				this.feasiblity = false;
			}else {
				this.feasiblity = true;
			}
			if(is_print_information) {
				if(check_time()==false) {
					while(true) {}
				}
			}
			//更新最优解
			boolean is_update_best = update_best_solution();
			
			//确定新的排序方法
			if(is_update_best) { //更新解成功则对新解调用recal_accumulate_time
				//System.out.println("    update_best");
				CAT_model = 1;
				continue;
			}
			else if(CAT_model==1 && is_ban_CAT2==false) { //1方式更新解失败
				load_copy_solution(this.best_solution); //加载最优解
				CAT_model = 2;
				continue;
			}else{ //0或2方式更新解失败
				if(is_ban_enhance==false) { //执行enhance
					load_copy_solution(this.best_solution); //加载最优解
					enhance(); //深度优化makespan
					if(update_best_solution()==false) { //enhance失败:未发现更优解
						CAT_model = 0; 
					}
					else { //enhance成功:发现更优解
						CAT_model = 1;
						continue;
					}
				}
			}
			//System.out.println();
			//舍弃当前最先考虑的机器类型,进入下一轮迭代
			this.update_best_solution(best_copy); //本轮最优与本轮之前的最优解best_copy作比较，保留最优
			CAT_model = 0; 
			start_index++;
			if(start_index==limit_iter) break;
		}
		//返回最优解	
		load_copy_solution(this.best_solution);
		return this.trans_2_solution();
	}
	
	//输入初始解,依据初始解的信息,执行调度
	public Solution schedule(Workflow wf,Solution s,int ret_arr[]) {
		if(TaskArray==null) { //尚未构建问题信息
			set_rand_seed(wf.seed); //added by fan, fix random seed to analysis
			//构建问题模型,去除被支配机器类型
			Build_problem_condiction(wf);
			//构建算法环境，初始化相关变量
			Build_alg_condiction();
		}
		//加载外部解
		load_external_solution(s);
		//初始化最优解
		this.best_solution.copy_inf(this);
		//写循环
		//boolean is_update_best = false; //is_recal_accumulate_time策略变量
		int CAT_model = 0;
		
		int FES = 0; //评价次数
		int start_index = 0; //每轮迭代只考虑vm_types_overall_descend[start_index]以及后面的机器类型
		while(start_index<1) {
			
			//选机器，选取结果存放至this.leased_VM_types,this.leased_VM_num
			lease_VM(this);
			//清空当前解
			clear_solution();
			
			if(is_ban_CAT1==true && CAT_model==1) {
				CAT_model=2;
			}
			//任务排序
			if(CAT_model==0) cal_accumulate_time();
			else if(CAT_model==1) recal_accumulate_time();
			else if(CAT_model==2) rerecal_accumulate_time();
			else {
				System.out.println("line111: CAT_model ERROR,CAT_model = "+CAT_model);
				while(true) {;}
			}
			
			
			task_sort_list = desc_sort_tasks(this.accumulate_time);
			//给任务分配机器
			assign_vm(task_sort_list);
			//计算cost
			this.cost = total_cost();
			//计算makespan
			this.makespan = total_maskspan();
			//计算可行性
			if(this.cost>=this.budget+tiny_num) {
				this.feasiblity = false;
			}else {
				this.feasiblity = true;
			}
			if(is_print_information) {
				if(check_time()==false) {
					while(true) {}
				}
			}
			//更新评价次数
			FES++;
			//更新最优解
			boolean is_update_best = update_best_solution();
			
			//确定新的排序方法
			if(is_update_best) { //更新解成功则对新解调用recal_accumulate_time
				CAT_model = 1;
				continue;
			}
			else if(CAT_model==1 && is_ban_CAT2==false) { //1方式更新解失败
				load_copy_solution(this.best_solution); //加载最优解
				CAT_model = 2;
				continue;
			}else{ //0或2方式更新解失败
				if(is_ban_enhance==false) { //执行enhance
					load_copy_solution(this.best_solution); //加载最优解
					enhance(); //深度优化makespan
					if(update_best_solution()==false) { //enhance失败:未发现更优解
						CAT_model = 0; 
					}
					else { //enhance成功:发现更优解
						CAT_model = 1;
						continue;
					}
				}
			}
			//System.out.println();
			//舍弃当前最先考虑的机器类型,进入下一轮迭代
			start_index++;
		}
		//返回最优解
		ret_arr[0] = FES;
		load_copy_solution(this.best_solution);
		return this.trans_2_solution();
	}
	
	private boolean check_time() {
		for(int tid=0;tid<this.task_num;tid++) {
			double st = this.start_time[tid];
			double ft = this.finish_time[tid];
			double et = this.execute_time[tid];
			int vm = this.Vm_of_task[tid];
			int vm_rank = this.execute_rank_on_its_vm[tid];
			//检查et
			if(Math.abs(ft-st-et)>tiny_num) {
				System.out.println("task "+tid+" et error");
				return false;
			}
			//st大于等于所有父任务的ft+传输时间
			for(int pt:this.parent_tasks_id.get(tid)) {
				double pt_ft = this.finish_time[pt];
				double arrive_time = pt_ft;
				if(this.Vm_of_task[pt]!=this.Vm_of_task[tid]) {
					arrive_time += this.TransRequireTime[pt][tid];
					if(arrive_time>st+tiny_num) {
						System.out.println("task "+pt+" -> task "+tid+" error");
						return false;
					}
				}
			}
			//ft小于等于所有子任务的st-传输时间
			for(int ct:this.child_tasks_id.get(tid)) {
				double ct_st = this.start_time[ct];
				double output_time = ct_st;
				if(this.Vm_of_task[tid]!=this.Vm_of_task[ct]) {
					output_time -= this.TransRequireTime[tid][ct];
				}
				if(output_time<ft-tiny_num) {
					System.out.println("task "+tid+" -> task "+ct+" error");
					return false;
				}
			}
			
			if(tid!=this.entry_task_id && tid!=this.exit_task_id) {
				//st大于等于同一机器上上一个执行任务的ft
				if(vm_rank>1) {
					int last_task = this.Tasks_of_vm[vm][vm_rank-1];
					if(this.finish_time[last_task]>st+tiny_num) {
						System.out.println("vm "+vm+" :task "+last_task+" -> task "+tid+" error");
						return false;
					}
				}
				//ft小于等于同一机器下一个执行任务的st
				if(vm_rank<this.Tasks_of_vm[vm][0]) {
					int next_task = this.Tasks_of_vm[vm][vm_rank+1];
					if(this.start_time[next_task]<ft-tiny_num) {
						System.out.println("vm "+vm+" :task "+tid+" -> task "+next_task+" error");
						return false;
					}
				}
			}
			
		}
		return true;
	}
	
	private double[] free_time(double st[],double ft[]) {
		//初始化过程变量
		double FRT[] = new double[this.task_num];
		double boot_time[] = new double[this.used_vm_num]; //每个机器当前启动时间
		Arrays.fill(boot_time, this.finish_time[this.exit_task_id]);
		//获取任务处理顺序
		ArrayList< Integer > task_list = desc_sort_tasks(this.finish_time); //降序
		//开始结束任务
		st[this.entry_task_id] = this.start_time[this.entry_task_id];
		ft[this.entry_task_id] = this.finish_time[this.entry_task_id];
		st[this.exit_task_id] = this.start_time[this.exit_task_id];
		ft[this.exit_task_id] = this.finish_time[this.exit_task_id];
		//遍历所有real task
		for(int i=0;i<this.task_num-2;i++) {
			int t = task_list.get(i);
			//System.out.println("st["+t+"]="+this.start_time[t]);
			//System.out.println("ft["+t+"]="+this.finish_time[t]);
			int vm = this.Vm_of_task[t];
			//计算反向分配机器时,计算在使用机器vm的情况下,任务t的所有子任务结果要求t最早开始传输数据时间
			double min_ot = Double.MAX_VALUE;
			for(int tc:this.child_tasks_id.get(t)) { //遍历每一个子任务tc
				//计算tc数据到达时间arrive_time
				double output_time = st[tc];
				if(this.Vm_of_task[tc]!=vm)	{
					output_time -= this.TransRequireTime[t][tc];
				}
				//更新min_ot
				min_ot = Math.min(output_time, min_ot);
			}
			//计算反向分配机器的结束时间,开始时间
			ft[t] = Math.min(min_ot, boot_time[vm]);
			st[t] = ft[t] - this.execute_time[t];
			//更新机器开始处理首任务时间
			boot_time[vm] = st[t];
			//计算浮动时间
			FRT[t] = st[t] - this.start_time[t];
			//System.out.println("  use VM:"+vm);
			//System.out.println("  new st:"+st[t]);
			//System.out.println("  new ft:"+ft[t]);
			//System.out.println("  free_time:"+FRT[t]);
			//System.out.println();
		}
		return FRT;
	}
	
	//对所有任务排序
	private ArrayList<Integer> rank_tasks_use_significance(double FRT[],int Arr[]) {
		//标记所有real_task所在的关键路径排名path_id
		ArrayList<Integer> task_list1 = this.ascd_sort_tasks(FRT); //按照任务浮动时间升序排序
		int path_id[] = new int[this.task_num];//各个任务关键路径编号
		int pid = 0; //当前路径编号
		path_id[this.entry_task_id] = path_id[this.exit_task_id] = pid;
		int last_task = this.entry_task_id;
		int key_task_num = 0;
		for(int i=0;i<task_list1.size();i++) { //确定关键路径编号
			int current_task = task_list1.get(i);
			if(FRT[current_task]-FRT[last_task]<this.tiny_num) {
				path_id[current_task] = pid;
				FRT[current_task] = FRT[last_task]; //去除浮点数极小误差
				if(pid==0) key_task_num++;
			}else {
				pid--;
				path_id[current_task] = pid;
			}
			last_task = current_task;
		}
		for(int t=0;t<this.task_num;t++) { //路径编号转换成1-n, n为关键路径对应编号
			path_id[t] -= pid;
			path_id[t]++;
		}
		int max_path_id = -pid + 1;
		double max_ts = -1.0;
		//计算每个任务可达任务的pid之和ps
		int ps[] = new int[this.task_num];
		for(int t=0;t<this.task_num;t++) {
			max_ts = Math.max(max_ts, this.TaskArray[t].getTaskSize());
			ps[t] = 0;
			for(int i=1;i<=this.pass_tasks[t][0];i++) {
				int tp = this.pass_tasks[t][i];
				ps[t] += path_id[tp];
			}
			//System.out.println();
			for(int i=1;i<=this.arrive_tasks[t][0];i++) {
				int tp = this.arrive_tasks[t][i];
				ps[t] += path_id[tp];
			}
		}
		
		//所有任务排序: 主指标：path_id(越大越好,降序),次指标：ps(越大越好,降序),次次指标:task_size(越大越好,降序)
		double indicitor[] = new double[this.task_num];
		for(int t=0;t<this.task_num;t++) {
			indicitor[t] = path_id[t];
			indicitor[t] += ps[t]/(1.0*max_path_id*this.task_num);
			indicitor[t] += tiny_num * this.TaskArray[t].getTaskSize()/max_ts;
		}
		ArrayList<Integer> task_list2 = this.desc_sort_tasks(indicitor);
		Arr[0] = key_task_num;
		/*
		for(int i=0;i<task_list2.size();i++) {
			int t = task_list2.get(i);
			System.out.println("t"+t+" : "+indicitor[t]);
			System.out.println("  pid"+" : "+path_id[t]);
			System.out.println("  ps"+" : "+ps[t]);
			System.out.println("  task_size"+" : "+this.TaskArray[t].getTaskSize());
		}	
		*/
		return task_list2;
	}
	
	//在已有VM的前提下,尝试降低makespan
	private void enhance() {
		//boolean is_improve = false;
		//对所有任务排序,主指标：path_id(越大越好,降序),次指标：ps(越大越好,降序),次次指标:task_size(越大越好,降序)
		double st[] = new double[this.task_num]; //反方向的start_time
		double ft[] = new double[this.task_num]; //反方向的finish_time
		double FRT[] = free_time(st,ft); //计算st,ft以及浮动时间FRT
		int Arr[] = new int[1];
		ArrayList<Integer> task_list2 = rank_tasks_use_significance(FRT,Arr);
		int key_task_num = Arr[0];
		//执行插入操作,尝试将关键任务kt改用非关键任务ut的机器,并插入到ut之前
		for(int i=0;i<key_task_num;i++) {
			int kt = task_list2.get(i);
			//System.out.println("key_task = "+kt);
			for(int j=task_list2.size()-1;j>=key_task_num;j--) {
				int ut = task_list2.get(j);
				int uvm = this.Vm_of_task[ut];
				//System.out.println("  task = "+ut);
				//要求kt和ut互相不可达,不满足该要求则继续遍历
				if(can_arrive[kt][ut] || can_arrive[ut][kt]) {
					//System.out.println("    connected, continue");
					continue;
				}
				//求出ut可腾出的空闲时段
				double s1 = prior_task_ft(ut,kt);
				double s2 = st[ut];
				//System.out.println("    idle span:["+s1+","+s2+"]");
				double max_at = max_arrive_time(kt,uvm); //计算kt使用ut的机器uvm后,所有父任务结果的到达时间max_at
				double min_st = max_at; //最早开始时间
				double max_ft = min_output_time(kt,uvm,st); //最晚结束时间
				
				double kt_new_st = Math.max(min_st, s1); //kt新的开始时间
				double kt_new_max_ft = Math.min(max_ft, s2); //kt新的最大结束时间
				//计算kt是否可移植到该时段
				if((kt_new_max_ft-kt_new_st)*this.VM_Array[uvm].getSpeed()>this.TaskArray[kt].getTaskSize()) {
					//移植时段可以处理kt
					st[kt] = kt_new_st; //关键任务新的开始时间
					this.Vm_of_task[kt] = uvm; //各个任务新的开始机器
					
					
					//清空Tasks_of_vm
					for(int vm_id=0;vm_id<2*this.task_num;vm_id++) {
						Tasks_of_vm[vm_id][0]=0;
					}
					
					assign_vm(ascd_sort_tasks(st),Vm_of_task);
					this.cost = total_cost();
					this.makespan = total_maskspan();//计算makespan
					//计算可行性
					if(this.cost>=this.budget+tiny_num) this.feasiblity = false;	
					else this.feasiblity = true;
					//检查解
					if(is_print_information) {
						if(check_time()==false) {
							while(true) {}
						}
					}
					return;
					
				}else { //移植时段不足以处理kt
					continue;
				}
				
				//是则移植,计算新解的评价值,变优则接受,is_improve = true,停止遍历
				
				//否则不接受新解,还原解,继续遍历
				
				
			}
			//System.out.println();
		}
		
		
		
		
		//System.out.println();
		
		return;
	}
	
	//在相同机器上ut上一个任务的结束时间,ut为首任务则返回开机时间
	private double prior_task_ft(int ut,int kt) {
		int urank = this.execute_rank_on_its_vm[ut];
		int uvm = this.Vm_of_task[ut];
		if(urank==1) {
			double bt = vm_boot_time(uvm);
			double dt = vm_shutdown_time(uvm);
			return dt - this.ceil_front_time(dt-bt)+this.max_input_time[kt];
		}
		else {
			int prior_task = this.Tasks_of_vm[uvm][urank-1];
			return this.finish_time[prior_task];
		}
	}
	
	//在相同机器上ut上一个任务的结束时间,ut为首任务则返回开机时间
	private double next_task_ft(int ut,int kt) {
		int urank = this.execute_rank_on_its_vm[ut];
		int uvm = this.Vm_of_task[ut];
		if(urank==this.Tasks_of_vm[uvm][0]) {
			
			double bt = vm_boot_time(uvm);
			double dt = vm_shutdown_time(uvm);
			return bt + this.ceil_front_time(dt-bt)-this.max_output_time[kt];
		}
		else {
			int prior_task = this.Tasks_of_vm[uvm][urank-1];
			return this.finish_time[prior_task];
		}
	}
	
	//使用当前解更新最优解
	private boolean update_best_solution() {
		boolean is_update = false;
		if(this.feasiblity==true) { //当前解可行
			if(best_solution.feasiblity==false || best_solution.makespan>this.makespan+tiny_num) {
				is_update = true;
			}
		}else { //当前解不可行
			if(best_solution.feasiblity==false && best_solution.cost>this.cost+tiny_num) {
				is_update = true;
			}
		}
		//更新最优解全部信息
		if(is_update) {
			this.best_solution.copy_inf(this);
		}
		return is_update;
	}
	
	//使用输入解cs更新最优解
	private boolean update_best_solution(copy_sol cs) {
		boolean is_update = false;
		if(cs.feasiblity==true) { //cs可行
			if(best_solution.feasiblity==false || best_solution.makespan>cs.makespan+tiny_num) {
				is_update = true;
			}
		}else { //cs不可行
			if(best_solution.feasiblity==false && best_solution.cost>cs.cost+tiny_num) {
				is_update = true;
			}
		}
		//更新最优解全部信息
		if(is_update) {
			this.best_solution.copy_inf(cs);
		}
		return is_update;
	}
	
	//加载复制解
	private void load_copy_solution(copy_sol s) {
		this.cost = s.cost;
		this.makespan = s.makespan;
		this.feasiblity = s.feasiblity;
		this.used_vm_num = s.used_vm_num;
		//复制各个成员信息
		for(int t=0;t<task_num;t++) {
			this.Vm_of_task[t] = s.Vm_of_task[t];
			this.start_time[t] = s.start_time[t];
			this.finish_time[t] = s.finish_time[t];
			this.execute_time[t] = s.execute_time[t];
			execute_rank_on_its_vm[t] = s.execute_rank_on_its_vm[t];
		}
		//复制VM_Array
		for(int i=0;i<s.used_vm_num;i++) {
			this.VM_Array[i] = new VM(s.VM_Array[i].getType());
		}
		//复制Tasks_of_vm
		for(int t1=0;t1<task_num;t1++) {
			for(int t2=0;t2<=task_num;t2++) {
				this.Tasks_of_vm[t1][t2] = s.Tasks_of_vm[t1][t2];
			}
		}
		if(is_print_information) {
			if(check_time()==false) {
				while(true) {}
			}
		}
	}
	
	
	
	//将当前解转化为Solution格式
	private Solution trans_2_solution() {
		
		Solution solution = new Solution();
		//entry_task
		double min_st = Double.MAX_VALUE;
		int vm0 = -1;
		for(int ct:this.child_tasks_id.get(this.entry_task_id)) {
			if(this.start_time[ct]<min_st) {
				min_st = this.start_time[ct];
				vm0 = this.Vm_of_task[ct];
			}
		}
		solution.addTaskToVM(this.VM_Array[vm0],  this.TaskArray[this.entry_task_id], min_st, true);
		
		//遍历每一个机器
		for(int vm=0;vm<this.used_vm_num;vm++) {
			//遍历在该机器上处理的每一个任务
			for(int i=1;i<=this.Tasks_of_vm[vm][0];i++) {
				int tid = this.Tasks_of_vm[vm][i];
				solution.addTaskToVM(this.VM_Array[vm], this.TaskArray[tid], this.start_time[tid], true);
			}
		}
		
		//exit_task
		double max_ft = -Double.MAX_VALUE;
		int vm1 = -1;
		for(int pt:this.parent_tasks_id.get(this.exit_task_id)) {
			if(this.finish_time[pt]>max_ft) {
				max_ft = this.finish_time[pt];
				vm1 = this.Vm_of_task[pt];
			}
		}
		solution.addTaskToVM(this.VM_Array[vm1],  this.TaskArray[this.exit_task_id], max_ft, true);
		
		if(is_print_information) System.out.println(solution.calcMakespan());
		if(is_print_information) System.out.println(solution.calcCost());
		return solution;
	}
	
	//清空当前解
	private void clear_solution() {
		//初始化used_vm_num
		this.used_vm_num = 0;
		//初始化Tasks_of_vm
		for(int vm_id=0;vm_id<2*this.task_num;vm_id++) {
			Tasks_of_vm[vm_id][0]=0;
		}
		//初始化VM序号
		VM.setInternalId(0);
		//清空execute_rank_on_its_vm
		Arrays.fill(execute_rank_on_its_vm, -1);
		
		
		if(is_print_information) System.out.println("end fun clear_solution");
		
		
	}
	
	private double total_maskspan() {
		return this.finish_time[this.exit_task_id];
	}
	
	private double total_cost() {
		double cost = 0.0;
		for(int v=0;v<this.used_vm_num;v++) {
			int vm_type = this.VM_Array[v].getType();
			double bt = vm_boot_time(v);
			double dt = vm_shutdown_time(v);
			double hour = this.ceil_front_time(dt-bt) / VM.INTERVAL;
			double c = VM.UNIT_COSTS[vm_type] * hour;
			cost += c;
		}
		return cost;
	}
	
	//分配机器
	private void assign_vm(ArrayList<Integer> task_sort_list) {
		//初始化评价指标
		this.cost = 0.0;
		makespan = Double.MAX_VALUE; //完成调度时间
		feasiblity = false;
		//设定entry_task的起止时间和分配机器
		this.start_time[this.entry_task_id] = 0.0;
		this.finish_time[this.entry_task_id] = 0.0;
		this.execute_time[this.entry_task_id] = 0.0;
		this.Vm_of_task[this.entry_task_id] = -1; //无实际使用机器
		//给所有real task分配机器
		for(int tid:task_sort_list) {
			if(this.is_print_information)	System.out.println("tid = "+tid);
			//初始化最快机器信息
			double fastest_tarr[] = null; //存放最快机器的起止时间以及新增cost
			int fastest_varr[] = null; //存放最快机器的机器编号，类型，新旧(是否为老机器),插入位置
			//初始化最快免费机器信息
			double free_tarr[] = null; //存放最快免费机器的起止时间以及新增cost
			int free_varr[] = null; //存放最快免费机器的机器编号，类型，新旧(是否为老机器),插入位置
			//遍历所有旧机器
			for(int vj=0;vj<this.used_vm_num;vj++) {
				double t_arr[] = new double[3]; //起[0]止[1]时间以及新增cost[2]
				int v_arr[] = new int[4];//[0]机器编号，[1]类型，[2]新旧(是否为老机器),[3]插入位置
				v_arr[0] = vj;
				v_arr[1] = this.VM_Array[vj].getType();
				v_arr[2] = 1;
				v_arr[3] = cal_ft_and_addcost(tid,vj,t_arr);
				
				//System.out.println(t_arr);
				//更新fastest_tarr, free_tarr
				if(t_arr!=null) {
					//更新fastest_tarr
					if(fastest_tarr==null || t_arr[1]<fastest_tarr[1]) {
						fastest_varr = v_arr;
						fastest_tarr = t_arr;
					}
					//更新free_tarr
					if(t_arr[2]<tiny_num && (free_tarr==null || t_arr[1]<free_tarr[1])) {
						free_varr = v_arr;
						free_tarr = t_arr;
					}
				}
			}
			//遍历所有新机器
			double max_at = max_arrive_time(tid,-1); //计算使用新机器情况下,ti所有父任务结果的到达时间max_at
			for(int vmtype:leased_VM_types) {
				if(this.available_VM_hour[vmtype]<=0) {
					continue;
				}
				double et = this.TaskArray[tid].getTaskSize() / VM.SPEEDS[vmtype];
				//生成t_arr
				double t_arr[] = new double[3]; //起[0]止[1]时间以及新增cost[2]
				t_arr[0] = max_at;
				t_arr[1] = max_at+et;
				double hour = this.ceil_front_time(et+VM.LAUNCH_TIME+this.max_input_time[tid]+this.max_output_time[tid] ) / VM.INTERVAL;
				t_arr[2] = VM.UNIT_COSTS[vmtype] * hour;
				//生成v_arr
				int v_arr[] = new int[4];//[0]机器编号，[1]类型，[2]新旧(是否为老机器),[3]插入位置
				v_arr[0] = -1;
				v_arr[1] = vmtype;
				v_arr[2] = 0;
				v_arr[3] = 1;
				//更新fastest_tarr
				if(fastest_tarr==null || t_arr[1]<fastest_tarr[1]) {
					fastest_varr = v_arr;
					fastest_tarr = t_arr;
				}
			}
			
			//选择机器
			int need_lease_hour = task_lease_hour(fastest_varr,fastest_tarr);
			int fastest_vm_type = fastest_varr[1];
			if(free_tarr==null || need_lease_hour<=this.available_VM_hour[fastest_vm_type]) {
				//最快机器剩余数量充足或者无免费机器可用,使用最快机器
				alloc_front_task(tid,fastest_varr,fastest_tarr);
			}else { //使用免费机器
				alloc_front_task(tid,free_varr,free_tarr);
			}
			//System.out.println();
		}
		
		
		//设定exit_task的起止时间和分配机器
		this.start_time[this.exit_task_id] = this.max_arrive_time(exit_task_id, -1);
		this.finish_time[this.exit_task_id] = this.start_time[this.exit_task_id];
		this.execute_time[this.exit_task_id] = 0.0;
		this.Vm_of_task[this.exit_task_id] = -1; //无实际使用机器
		
		//启用未被使用的机器
		lease_empty_VMs();
	}
	
	//分配机器
	private void assign_vm(ArrayList<Integer> task_sort_list,int vm_of_task[]) {
		//初始化评价指标
		this.cost = 0.0;
		makespan = Double.MAX_VALUE; //完成调度时间
		feasiblity = false;
		//设定entry_task的起止时间和分配机器
		this.start_time[this.entry_task_id] = 0.0;
		this.finish_time[this.entry_task_id] = 0.0;
		this.execute_time[this.entry_task_id] = 0.0;
		this.Vm_of_task[this.entry_task_id] = -1; //无实际使用机器
		//给所有real task分配机器
		for(int tid:task_sort_list) {
			if(this.is_print_information)	System.out.println("tid = "+tid);
			//直接指派旧机器vm_of_task[tid]
			int vj = vm_of_task[tid];
			double t_arr[] = new double[3]; //起[0]止[1]时间以及新增cost[2]
			int v_arr[] = new int[4];//[0]机器编号，[1]类型，[2]新旧(是否为老机器),[3]插入位置
			v_arr[0] = vj;
			v_arr[1] = this.VM_Array[vj].getType();
			v_arr[2] = 1;
			v_arr[3] = cal_ft_and_addcost(tid,vj,t_arr);
			//执行分配
			alloc_front_task(tid,v_arr,t_arr);
		}
		//设定exit_task的起止时间和分配机器
		this.start_time[this.exit_task_id] = this.max_arrive_time(exit_task_id, -1);
		this.finish_time[this.exit_task_id] = this.start_time[this.exit_task_id];
		this.execute_time[this.exit_task_id] = 0.0;
		this.Vm_of_task[this.exit_task_id] = -1; //无实际使用机器
		
		//启用未被使用的机器
		lease_empty_VMs();
	}
	
	//启用未被使用的机器
	private void lease_empty_VMs() {
		for(int vmtype:leased_VM_types) {
			for(int i=0;i<this.available_VM_hour[vmtype];i++) {//有几台就租用几台
				add_empty_vm(vmtype);
			}
		}
	}
	
	//新增一个类型为type的空机器
	private void add_empty_vm(int type) {
		if(this.used_vm_num==this.task_num) return;
		int new_vm = this.used_vm_num++;
		this.VM_Array[new_vm] = new VM(type);
		this.Tasks_of_vm[new_vm][0] = 0; //设置为不处理任何任务
		this.available_VM_hour[type]--;
		if(this.is_print_information) {
			System.out.println("lease empty VM "+new_vm+", type = "+type);
		}
	}
	
	//计算需要额外租赁的时段数目
	private int task_lease_hour(int varr[],double tarr[]) {
		int vm_type = varr[1];
		return (int)(tarr[2]/VM.UNIT_COSTS[vm_type]+tiny_num);
	}
	
	
	//指定机器以及所有要更新的参数,给sft分配机器
	private void alloc_front_task(int tid, int v_arr[],double t_arr[]) {
		//确定机器编号，旧机器则直接使用;新机器则创建编号，更新used_vm_num,this.VM_Array[],front_vm_list
		int vm = -1;
		if(v_arr[2]==1) { //使用已有机器 //[0]机器编号，[1]类型，[2]新旧(是否为老机器),[3]插入位置
			vm = v_arr[0];
		}else { //使用新机器
			vm = this.used_vm_num++;
			this.VM_Array[vm] = new VM(v_arr[1]);
		}
		//更新this.Vm_of_task
		this.Vm_of_task[tid] = vm;			
		//更新this.start_time，this.finish_time
		this.start_time[tid] = t_arr[0];
		this.finish_time[tid] = t_arr[1];
		this.execute_time[tid] = t_arr[1]-t_arr[0];
		//更新this.Tasks_of_vm[vm][]
		this.Tasks_of_vm[vm][0]++;
		int ix = this.Tasks_of_vm[vm][0];
		while(ix>v_arr[3]) {
			this.Tasks_of_vm[vm][ix] = this.Tasks_of_vm[vm][ix-1];
			execute_rank_on_its_vm[ Tasks_of_vm[vm][ix] ] = ix;
			--ix;
		}
		this.Tasks_of_vm[vm][v_arr[3]] = tid;
		execute_rank_on_its_vm[tid] = v_arr[3];
		//更新available_VM_hour
		this.available_VM_hour[v_arr[1]] -= task_lease_hour(v_arr,t_arr);
		//打印过程信息
		if(is_print_information) {
			
			if(v_arr[2]==1) 	System.out.println("assign old vm "+vm +"(type = "+ this.VM_Array[vm].getType()+")"+" to front task "+tid);
			else	System.out.println("assign new vm "+vm +"(type = "+ this.VM_Array[vm].getType()+")"+" to front task "+tid);
		}
		if(is_print_information) System.out.println("	["+String.format("%.2f", this.start_time[tid])+","+String.format("%.2f", this.finish_time[tid])+"]");
		if(is_print_information) System.out.println("	tloc = "+v_arr[3]);
		if(is_print_information) {
			System.out.print("	 Tasks_of_vm:");
			for(int i=1;i<=this.Tasks_of_vm[vm][0];i++) {
				System.out.print(this.Tasks_of_vm[vm][i]+" ");
			}
			//System.out.println();
		}
		
		
		if(is_print_information) System.out.println("	add_cost = "+t_arr[2]);
		if(is_print_information) System.out.println("");
	}
	
	
	//计算将任务ti分配给机器vj的开始时间,完成时间以及新增cost,存放在t_arr[0]-[2],并返回在vj上插入时段的位置
	private int cal_ft_and_addcost(int tid,int vj,double t_arr[]) {
		//double return_arr[] = new double[2];
		double max_at = max_arrive_time(tid,vj); //计算ti所有父任务结果的到达时间max_at
		//计算开始时间
		double et = this.TaskArray[tid].getTaskSize() / this.VM_Array[vj].getSpeed();
		int index = fastest_available_period_in_exit_vm(tid,vj,max_at,Double.MAX_VALUE,et,t_arr);
		if(index==-1) {
			t_arr = null;
		}
		return index;
	}
	
	//计算在使用机器vj的情况下,任务ti的所有父任务结果的到达时间
	private double max_arrive_time(int ti,int vj) {
		double max_at = -Double.MAX_VALUE;
		for(int tp:this.parent_tasks_id.get(ti)) { //遍历每一个父任务tp
			//计算tp数据到达时间arrive_time
			double arrive_time = this.finish_time[tp];
			if(this.Vm_of_task[tp]!=vj)	{
				arrive_time += this.TransRequireTime[tp][ti];
			}
			//更新st
			max_at = Math.max(arrive_time, max_at);
		}
		return max_at;
	}
	
	//计算任务ti在使用机器vj的情况下,任务ti的应该开始传输给各个子任务结果的最小时间
	private double min_output_time(int ti,int vj,double st[]) {
		double min_ot = Double.MAX_VALUE;
		for(int ct:this.child_tasks_id.get(ti)) {
			double ot = st[ct];
			if(this.Vm_of_task[ct]!=vj) {
				ot -= this.TransRequireTime[ti][ct];
			}
			if(ot < min_ot) {
				min_ot = ot;
			}
		}
		return min_ot;
	}

	
	//给定机器vm,找到在[min_st,max_ft]时段内一个长度为et的最快空闲时段,该时段起止时间以及新增cost存放在t_arr中，是则返回空闲时段处在所处理的第几个任务之后，无空闲时段则返回-1
	private int fastest_available_period_in_exit_vm(int tid,int vm,double min_st,double max_ft,double et,double t_arr[]) {
		t_arr[2] = Double.MAX_VALUE; //所有方案的最小cost
		int index = -1; //返回值，空闲时段处在所处理的第几个任务之后，无空闲时段则返回-1
		int period_num = this.Tasks_of_vm[vm][0]+1; //空闲时段个数
		double t1[] = new double[period_num]; //各个时段的开始时间
		double t2[] = new double[period_num]; //各个时段的终止时间
		//生成t1 t2
		t1[0] = 0.0;
		t2[period_num-1] = Double.MAX_VALUE;
		for(int i=1;i<=this.Tasks_of_vm[vm][0];i++) {
			int task = this.Tasks_of_vm[vm][i];
			t1[i] = this.finish_time[task]; //第i个task的结束之间为第i个时段的开始时间
			t2[i-1] = this.start_time[task]; //第i个task的开始时间为第i-1个时段的终止时间
		}
		
		//遍历各个空闲时段
		for(int i=0;i<period_num;i++) {
			if(t2[i]<=min_st+tiny_num) { //当前区间在[min_st,max_ft]左侧，继续遍历下一个
				continue;
			}else if(t1[i]>=max_ft-tiny_num) { //当前区间在[min_st,max_ft]右侧，停止遍历
				break;
			}
			else {
				double st = Math.max(t1[i], min_st); //当前时段可用开始时间
				double ft = Math.min(t2[i], max_ft); //当前时段可用终止时间
				if(ft-st>=et-tiny_num) { //可用时段可行，即时长大于等于et
					//计算占用机器vm上第i个空闲时段的[st,st+et]部分的新增cost
					t_arr[0] = st;
					t_arr[1] = st+et;
					//计算新增cost，存入t_arr[2]
					double old_bt = vm_boot_time(vm);
					double old_dt = vm_shutdown_time(vm);
					double old_hour = this.ceil_front_time(old_dt-old_bt) / VM.INTERVAL;
					
					double new_bt = Math.min(old_bt, st-VM.LAUNCH_TIME-this.max_input_time[tid]);
					double new_dt = Math.max(old_dt,st+et+this.max_output_time[tid]);
					double new_hour = this.ceil_front_time(new_dt-new_bt) / VM.INTERVAL;
					
					int vm_type = this.VM_Array[vm].getType();
					t_arr[2] = VM.UNIT_COSTS[vm_type] * (new_hour-old_hour);
					
					index = i;
					return index+1;
				}
			}
		}
		
		return index+1;
	}
	
	//机器开机时间
	private double vm_boot_time(int vm) {
		int t = this.Tasks_of_vm[vm][1];
		return this.start_time[t]-VM.LAUNCH_TIME-this.max_input_time[t];
	}
	
	//机器关机时间
	private double vm_shutdown_time(int vm) {
		int t = this.Tasks_of_vm[vm][Tasks_of_vm[vm][0]];
		return this.finish_time[t] + this.max_output_time[t];
	}
	
	//计算前向分配时,时间点time对应的收费时段数
	private double ceil_front_time(double time) {
		return Math.ceil( time/VM.INTERVAL ) * VM.INTERVAL;
	}
	
	
	//计算累计时间(任务处理时间使用avg_speed估计,边传输时间估计为不同机器之间的传输时间)
	private void cal_accumulate_time() {
		this.accumulate_time[this.exit_task_id] = 0.0;
		
		for(int i=this.pass_tasks[this.exit_task_id][0];i>=1;i--) {
			int t = this.pass_tasks[this.exit_task_id][i];
			double max_v = -1.0;
			for (int ct: this.child_tasks_id.get(t)) {
				double TT = this.TransRequireTime[t][ct];
				double v = this.accumulate_time[ct] + TT;
				max_v = Math.max(max_v, v);
			}
			double et = this.TaskArray[t].getTaskSize() / this.avg_speed;
			this.accumulate_time[t] = max_v + et;
			if(this.is_print_information) System.out.println("accumulate_time["+t+"] = "+this.accumulate_time[t]);
		}
		if(this.is_print_information) System.out.println("end func cal_accumulate_time");
	}
	
	//计算当前解的累计时间(任务处理时间使用处理时间,边传输时间估计为实际传输时间)
	private void recal_accumulate_time() {
		this.accumulate_time[this.exit_task_id] = 0.0;
		for(int i=this.pass_tasks[this.exit_task_id][0];i>=1;i--) {
			int t = this.pass_tasks[this.exit_task_id][i];
			double max_v = -1.0;
			for (int ct: this.child_tasks_id.get(t)) {
				double TT = 0.0;
				if(this.Vm_of_task[t]!=this.Vm_of_task[ct]) { //使用实际传输时间
					TT = this.TransRequireTime[t][ct];
				}
				double v = this.accumulate_time[ct] + TT;
				max_v = Math.max(max_v, v);
			}
			double et = this.execute_time[t]; //使用实际执行时间
			this.accumulate_time[t] = max_v + et;
			if(this.is_print_information) System.out.println("accumulate_time["+t+"] = "+this.accumulate_time[t]);
		}
		if(this.is_print_information) System.out.println("end func cal_accumulate_time");
	}
	
	//计算当前解的累计时间(直接估计为当前解每个任务 开始时间到exit_task_id的时间差 )
	private void rerecal_accumulate_time() {
		this.accumulate_time[this.exit_task_id] = 0.0;
		for(int i=this.pass_tasks[this.exit_task_id][0];i>=1;i--) {
			int t = this.pass_tasks[this.exit_task_id][i];
			this.accumulate_time[t] = this.finish_time[this.exit_task_id]-this.start_time[t];
			if(this.is_print_information) System.out.println("rere_cal_accumulate_time["+t+"] = "+this.accumulate_time[t]);
		}
		if(this.is_print_information) System.out.println("end func cal_accumulate_time");
	}
	
	//基于indicator指标给所有task降序排序
	private ArrayList<Integer> desc_sort_tasks(final double indicator[]){
		ArrayList< Integer > task_sort_list = new ArrayList< Integer > (this.task_num-2);
		for(int t=0;t<this.task_num;t++) {
			if(t!=this.entry_task_id && t!=this.exit_task_id) {
				task_sort_list.add(t);
			}
		}
		task_sort_list.sort(new Comparator< Integer >() {
		    @Override
		    public int compare(Integer o1, Integer o2) {
		        // 升序 返回1的时候进行位置交换
		        if (indicator[o1] > indicator[o2]) {
		            return -1;
		        } else if (indicator[o1] < indicator[o2]) {
		            return 1;
		        } else {
		            return 0;
		        }
		    }
		});
		
		return task_sort_list;
	}
	
	//基于double型indicator指标给所有task升序排序
	private ArrayList<Integer> ascd_sort_tasks(final double indicator[]){
		ArrayList< Integer > task_sort_list = new ArrayList< Integer > (this.task_num-2);
		for(int t=0;t<this.task_num;t++) {
			if(t!=this.entry_task_id && t!=this.exit_task_id) {
				task_sort_list.add(t);
			}
		}
		task_sort_list.sort(new Comparator< Integer >() {
		    @Override
		    public int compare(Integer o1, Integer o2) {
		        if (indicator[o1] > indicator[o2]) {
		            return 1;
		        } else if (indicator[o1] < indicator[o2]) {
		            return -1;
		        } else {
		            return 0;
		        }
		    }
		});
		return task_sort_list;
	}
	
	
	//设置随机种子,方便复现实验结果
	public void set_rand_seed(int seed) {
		this.rand = new Random(seed);
	}
	
	//根据输入的解选机器
	private void lease_VM(PACP_HEFT ps) {
//		清空leased_VM_types,leased_VM_num
		this.leased_VM_types = new ArrayList<Integer>();
		this.available_VM_hour = new int[VM.UNIT_COSTS.length];
		Arrays.fill(this.available_VM_hour, 0);
		double total_speed = 0.0; //总的机器速度
		int total_vm_num = 0;
		//	初始化剩余budget
		double remaining_budget = this.budget;
		//	计算最便宜机器的单位时段租用费用cheapest_uc
		//int cheapest_type = vm_types_ucost_descend[vm_types_ucost_descend.length-1];
		//double cheapest_uc = VM.UNIT_COSTS[cheapest_type];
		if(this.is_print_information) {
			System.out.println();
			System.out.println("---------------- lease_VM ------------------");
		}
		//迭代选机器
		for(int v=0;v<ps.used_vm_num;v++) {
			int vm_type = ps.VM_Array[v].getType(); //当前机器类型
			double tuc = VM.UNIT_COSTS[vm_type]; //对应价格
			if(remaining_budget>tuc-tiny_num) { //剩余budget足够则能租用几台就租用几台
				
				double bt = ps.vm_boot_time(v);
				double dt = ps.vm_shutdown_time(v);
				double hour = ceil_front_time(dt-bt) / VM.INTERVAL;
				int n = (int)(hour+tiny_num); //能租用的台数
				remaining_budget -= tuc*n; //更新剩余budget
				leased_VM_types.add(vm_type); //机器类型存放至leased_VM_types
				available_VM_hour[vm_type] = n; //机器数量存放至leased_VM_num
				total_speed += VM.SPEEDS[vm_type]*n; //更新total_speed
				total_vm_num += n; //更新total_vm_num
				if(this.is_print_information) {
					System.out.println("VM_types="+vm_type+",hour="+n);
				}
			}
		}
		if(total_vm_num==0) {
			System.out.println("ERROR in lease_VM, total_vm_num==0");
			while(true);
		}
		//计算
		this.avg_speed = total_speed / total_vm_num;
		if(this.is_print_information) {
			System.out.println("----------------------------------------");
			System.out.println();
		}
	}
	
	//调度前确定租用机器方案
	private void lease_VM(int start_index) {
		//初始化
		//	清空leased_VM_types,leased_VM_num
		this.leased_VM_types = new ArrayList<Integer>();
		this.available_VM_hour = new int[VM.UNIT_COSTS.length];
		Arrays.fill(this.available_VM_hour, 0);
		double total_speed = 0.0; //总的机器速度
		int total_vm_num = 0;
		//	初始化剩余budget
		double remaining_budget = this.budget;
		//	计算最便宜机器的单位时段租用费用cheapest_uc
		//int cheapest_type = vm_types_ucost_descend[vm_types_ucost_descend.length-1];
		//double cheapest_uc = VM.UNIT_COSTS[cheapest_type];
		if(this.is_print_information) {
			System.out.println();
			System.out.println("---------------- lease_VM ------------------");
		}
		//迭代选机器
		for(int i=start_index;i<vm_types_overall_descend.length;i++) {
			int vm_type = vm_types_overall_descend[i]; //当前机器类型
			double tuc = VM.UNIT_COSTS[vm_type]; //对应价格
			if(remaining_budget>tuc-tiny_num) { //剩余budget足够则能租用几台就租用几台
				int n = (int)(remaining_budget/tuc+tiny_num); //能租用的台数
				remaining_budget -= tuc*n; //更新剩余budget
				leased_VM_types.add(vm_type); //机器类型存放至leased_VM_types
				available_VM_hour[vm_type] = n; //机器数量存放至leased_VM_num
				total_speed += VM.SPEEDS[vm_type]*n; //更新total_speed
				total_vm_num += n; //更新total_vm_num
				if(this.is_print_information) {
					System.out.println("VM_types="+vm_type+",hour="+n);
				}
			}
		}
		if(total_vm_num==0) {
			System.out.println("ERROR in lease_VM, total_vm_num==0");
			while(true);
		}
		//计算
		this.avg_speed = total_speed / total_vm_num;
		if(this.is_print_information) {
			System.out.println("----------------------------------------");
			System.out.println();
		}
	}
	
	//将给定的解转化为当前解
	private void load_external_solution(Solution solution) {
		
		this.clear_solution();
		//used_vm_num
		this.used_vm_num = solution.keySet().size();
		//VM_Array
		int vid = 0;
		for(VM vm : solution.keySet()){
			vm.setId(vid);
			this.VM_Array[vid] = vm;
			//hm.put(vm.getId(), vid);
			vid++;
			//System.out.println(hm.get(vm.getId()));
		}
		
		//Vm_of_task,start_time,finish_time
		List<Allocation> alloc_list = new ArrayList<Allocation>(solution.getRevMapping().values());
		for(Allocation alloc:alloc_list) {
			int task_id = alloc.getTask().getId();
			this.start_time[task_id] = alloc.getStartTime();
			this.finish_time[task_id] = alloc.getFinishTime();
			this.execute_time[task_id] = this.finish_time[task_id]-this.start_time[task_id];
			
			if(task_id==this.entry_task_id || task_id==this.exit_task_id)	continue;
			int vm_id = alloc.getVM().getId();
			this.Vm_of_task[task_id] = vm_id;
		}
		
		//this.Tasks_of_vm
		ArrayList< Integer > task_list = ascd_sort_tasks(this.start_time); //升序排列
		for(int tid:task_list) {
			if(tid==this.entry_task_id || tid==this.exit_task_id)	continue;
			int vm_id = this.Vm_of_task[tid];
			
			this.Tasks_of_vm[vm_id][ ++this.Tasks_of_vm[vm_id][0] ] = tid;
			execute_rank_on_its_vm[tid] =this.Tasks_of_vm[vm_id][0];
		}
		
		//计算cost
		this.cost = total_cost();
		//计算makespan
		this.makespan = total_maskspan();
		//计算可行性
		if(this.cost>=this.budget+tiny_num) {
			this.feasiblity = false;
		}else {
			this.feasiblity = true;
		}
		
		if(is_print_information) {
			if(check_time()) System.out.println("check_time: no error");
			else {
				while(true)	System.out.println("check_time: ERROR!!!");
			}
		}else {
			if(check_time());
			else {
				while(true)	System.out.println("check_time: ERROR!!!");
			}
		}
		
		//System.out.println("end trans_solution_2_PACP");
	}
	
	//初始化算法环境
	private void Build_alg_condiction() {
		//初始化各个任务到exit_task的估计关键路径累计时间
		this.accumulate_time = new double[this.task_num];
		//初始化VM相关变量
		this.VM_Array = new VM[2*this.task_num];
		this.Vm_of_task = new int[this.task_num]; //每个任务被分配的机器
		this.Tasks_of_vm = new int[2*this.task_num][this.task_num+1]; //每个vm执行的所有task
		this.used_vm_num = 0;
		//start_time,finish_time,execute_time申请空间
		this.finish_time = new double[task_num]; //finish_time[i]表示第i个任务的完成时间
		this.start_time = new double[task_num]; //finish_time[i]表示第i个任务的完成时间
		this.execute_time = new double[task_num];//执行时间, execute_time[i] = finish_time[i] - start_time[i]
		this.execute_rank_on_its_vm = new int[this.task_num];
		//最优解信息
		this.best_solution = new copy_sol();
	}
	
	//构建问题模型
	private void Build_problem_condiction(Workflow wf) {
		//存储wf
		this.wf = wf;
		//设置最大调度budget
		this.budget = wf.getBudget();
		if(is_print_information) System.out.println("budget = "+this.budget);
		if(is_print_information) System.out.println("depth = "+wf.get(0).getDepth());
		//初始化任务数
		task_num = Task.get_internalId(); //wf中包含的任务个数
		//建立TaskArray
		TaskArray = new Task[task_num];//所有任务按照id存放到TaskArray中
		for(Task tk:wf) {
			TaskArray[tk.getId()] = tk;
		}
		//记录entry task以及 end task编号
		entry_task_id = task_num - 2; //依据Workflow中entry task被创建时的internalId
		exit_task_id = task_num - 1;   //依据Workflow中end task被创建时的internalId
		//建立task传输数据量矩阵TransDataSize,TransDataSize[i][j]存储任务i传递给任务j的数据量
		TransDataSize = new long[task_num][task_num];
		for(int i=0;i<task_num;i++) {
			for(int j=0;j<task_num;j++) {
				TransDataSize[i][j] = 0;
			}
		}
		//建立parent_tasks_id,存放每个任务所有前置任务的id,并构建is_child
		this.is_child = new boolean[this.task_num][this.task_num];
		for(int i=0;i<this.task_num;i++) {
			for(int j=0;j<this.task_num;j++) {
				this.is_child[i][j] = false;
			}
		}
		parent_tasks_id = new ArrayList<ArrayList<Integer>>();
		for(int i=0;i<task_num;i++) {
			ArrayList<Integer> tids = new ArrayList<Integer>();
			for(Edge inEdge : TaskArray[i].getInEdges()){
				int p_id = inEdge.getSource().getId();
				tids.add(p_id);
				TransDataSize[p_id][i] = inEdge.getDataSize();
				this.is_child[p_id][i] = true;
			}
			parent_tasks_id.add(tids);
		}
		//建立child_tasks_id,存放每个任务所有后继任务的id
		child_tasks_id = new ArrayList<ArrayList<Integer>>();
		for(int i=0;i<task_num;i++) {
			ArrayList<Integer> tids = new ArrayList<Integer>();
			for(Edge outEdge : TaskArray[i].getOutEdges()){
				int c_id = outEdge.getDestination().getId();
				tids.add(c_id);
				TransDataSize[i][c_id] = outEdge.getDataSize();
			}
			child_tasks_id.add(tids);
		}
		
		//建立task传输数据量矩阵TransRequireTime,TransRequireTime[i][j]存储任务i传递给任务j的数据所需时间
		TransRequireTime = new double[task_num][task_num];
		for(int i=0;i<task_num;i++) {
			for(int j=0;j<task_num;j++) {
				TransRequireTime[i][j] = 1.0*TransDataSize[i][j]/VM.NETWORK_SPEED;
			}
		}
		//确定候选VM_type,对于任意一个机器类型A，如果存在某一其他类型B在速度上比该类型快，且价格更低，则删除A
		boolean is_ban[] = new boolean[VM.TYPE_NO]; 
		Arrays.fill(is_ban, false);
		
		for(int i=0;i<VM.TYPE_NO;i++) {
			if(is_ban[i])	continue;
			for(int j=i+1;j<VM.TYPE_NO;j++) {
				if(VM.SPEEDS[i]>=VM.SPEEDS[j] && VM.UNIT_COSTS[i]<=VM.UNIT_COSTS[j]) {
					is_ban[j] = true;
					//System.out.println(i+" > "+j);
				}
				else if (VM.SPEEDS[i]<=VM.SPEEDS[j] && VM.UNIT_COSTS[i]>=VM.UNIT_COSTS[j]) {
					is_ban[i] = true;
					//System.out.println(j+" > "+i);
				}
			}
		}
		
	
		ArrayList<Integer> vm_types = new ArrayList<Integer>();
		for(int i=0;i<VM.TYPE_NO;i++) {
			if(is_ban[i]==false) {
				vm_types.add(i);
			}
		}
		//System.out.println(vm_types);
		//确定每个VM_Type的排名
		int used_vm_type[] = new int[vm_types.size()];
		vm_types_speed_descend = new int[vm_types.size()];
		vm_types_ucost_descend = new int[vm_types.size()];
		vm_types_overall_descend = new int[vm_types.size()];

		vm_type_speed_rank = new int[VM.TYPE_NO];
		vm_type_ucost_rank = new int[VM.TYPE_NO];
		vm_type_overall_rank = new int[VM.TYPE_NO];
		Arrays.fill(vm_type_speed_rank, VM.TYPE_NO+1);
		Arrays.fill(vm_type_ucost_rank, VM.TYPE_NO+1);
		Arrays.fill(vm_type_overall_rank, VM.TYPE_NO+1);
		
		for(int i=0;i<vm_types.size();i++) {
			int type = vm_types.get(i);
			if(is_print_information) System.out.println(type+" : "+VM.SPEEDS[type]+" \t "+VM.UNIT_COSTS[type] +" \t "+ VM.SPEEDS[type]/VM.UNIT_COSTS[type]);
			
			used_vm_type[i] = type;
			vm_types_speed_descend[i] = type;
			vm_types_ucost_descend[i] = type;
			vm_types_overall_descend[i] = type;
					
			vm_type_speed_rank[type] = i + 1;
			vm_type_ucost_rank[type] = i + 1;
			vm_type_overall_rank[type] = i + 1;
		}
		//确定每个VM_Type的SPEED排名
		for(int i=0;i<vm_types.size();i++) {
			int t1 = vm_types_speed_descend[i];
			for(int j=i+1;j<vm_types.size();j++) {
				int t2 = vm_types_speed_descend[j];
				if(VM.SPEEDS[t1]<VM.SPEEDS[t2]) {
					vm_types_speed_descend[i] = t2;
					vm_types_speed_descend[j] = t1;
					t1 = vm_types_speed_descend[i];
					t2 = vm_types_speed_descend[j];
				}
			}
			vm_type_speed_rank[t1] = i + 1;
		}
		
		//确定每个VM_Type的UNIT_COSTS排名
		for(int i=0;i<vm_types.size();i++) {
			int t1 = vm_types_ucost_descend[i];
			for(int j=i+1;j<vm_types.size();j++) {
				int t2 = vm_types_ucost_descend[j];
				if(VM.UNIT_COSTS[t1]<VM.UNIT_COSTS[t2]) {
					vm_types_ucost_descend[i] = t2;
					vm_types_ucost_descend[j] = t1;
					t1 = vm_types_ucost_descend[i];
					t2 = vm_types_ucost_descend[j];
				}
			}
			vm_type_ucost_rank[t1] = i + 1;
		}
		
		//确定每个VM_Type的Speed/UNIT_COSTS排名
		for(int i=0;i<vm_types.size();i++) {
			int t1 = vm_types_overall_descend[i];
			for(int j=i+1;j<vm_types.size();j++) {
				int t2 = vm_types_overall_descend[j];
				if(VM.SPEEDS[t1]/VM.UNIT_COSTS[t1]<VM.SPEEDS[t2]/VM.UNIT_COSTS[t2]-tiny_num) {
					vm_types_overall_descend[i] = t2;
					vm_types_overall_descend[j] = t1;
					t1 = vm_types_overall_descend[i];
					t2 = vm_types_overall_descend[j];
				}else if(VM.SPEEDS[t1]/VM.UNIT_COSTS[t1]<VM.SPEEDS[t2]/VM.UNIT_COSTS[t2]+tiny_num && VM.SPEEDS[t1]<VM.SPEEDS[t2]) {
					vm_types_overall_descend[i] = t2;
					vm_types_overall_descend[j] = t1;
					t1 = vm_types_overall_descend[i];
					t2 = vm_types_overall_descend[j];
				}
			}
			vm_type_overall_rank[t1] = i + 1;
		}
		
		/*
		//初始化predicted_speed
		this.predicted_speed = VM.SPEEDS[this.vm_types_speed_descend[0]];
		//初始化predicted_et
		this.predicted_et = new double[this.task_num];
		for(int t=0;t<this.task_num;t++) {
			this.predicted_et[t] = this.TaskArray[t].getTaskSize()/predicted_speed;
		}
		*/
		
		//初始化can_arrive，arrive_tasks,task_level_from_exit
		this.task_level_from_exit = new int[this.task_num];
		this.task_level_from_entry = new int[this.task_num];
		this.can_arrive = new boolean [this.task_num][this.task_num];  //can_arrive[i][j] 表示任务i是否可在有向无环图到达j
		this.arrive_tasks = new int[this.task_num][this.task_num+1]; //arrive_tasks[i][0]表示任务i可达的任务个数，后续罗列各个任务
		this.pass_tasks = new int[this.task_num][this.task_num]; 
		cal_arrive_and_level();
		
		//删除无用边
		delete_unnecessary_edge();
		
		
		//建立最大输入时间
		this.max_input_time = new double[this.task_num];
		for(int t=0;t<this.task_num;t++) {
			this.max_input_time[t] = 0.0;
			for(int pt:this.parent_tasks_id.get(t)) {
				if(this.TransRequireTime[pt][t]>this.max_input_time[t]) {
					this.max_input_time[t] = this.TransRequireTime[pt][t];
				}
			}
		}
		//建立最大输出时间
		this.max_output_time = new double[this.task_num];
		for(int t=0;t<this.task_num;t++) {
			this.max_output_time[t] = 0.0;
			for(int ct:this.child_tasks_id.get(t)) {
				if(this.TransRequireTime[t][ct]>this.max_output_time[t]) {
					this.max_output_time[t] = this.TransRequireTime[t][ct];
				}
			}
		}
		
		
		if(is_print_information) System.out.println("end Build_problem_condiction");
	}
	
	//基于parent_tasks_id和child_tasks_id, 计算 arrive_tasks,can_arrive, pass_tasks,task_level_from_entry,task_level_from_exit
	private void cal_arrive_and_level() {
		Arrays.fill(task_level_from_exit, 0);
		int remaining_out_edge_num[] = new int [this.task_num];
		int stack[] = new int [this.task_num+1];
		for(int i=0;i<this.task_num;i++) { //设置默认值
			this.arrive_tasks[i][0] = 0;
			for(int j=0;j<this.task_num;j++) {
				this.can_arrive[i][j] = false;
			}
			remaining_out_edge_num[i] = this.child_tasks_id.get(i).size();
		}
		//	自end_task开始，遍历整个DAG
		stack[0] = 1;
		stack[1] = this.exit_task_id;
		//this.task_level_from_exit[this.exit_task_id] = 1;
		while(stack[0]!=0) {
			//出栈
			int tid = stack[ stack[0]-- ];
			//System.out.println("pull " + tid);
			ArrayList<Integer> parents = this.parent_tasks_id.get(tid);
			for(int i=0;i<parents.size();i++) {
				int pt = parents.get(i);
				task_level_from_exit[pt] = Math.max(task_level_from_exit[tid]+1, task_level_from_exit[pt]);
				if(--remaining_out_edge_num[pt]==0) {
					stack[ ++stack[0] ] = pt; //压栈
					//System.out.println("\t push "+pt);
				}
				
				for(int j=1;j<=this.arrive_tasks[tid][0];j++) {
					int ct = this.arrive_tasks[tid][j];
					if(can_arrive[pt][ct]==false) {
						can_arrive[pt][ct] = true;
						this.arrive_tasks[pt][ ++this.arrive_tasks[pt][0] ] = ct;
						//System.out.println("\t " +pt+" --> "+ct);
					}
				}
				
				if(can_arrive[pt][tid]==false) {
					can_arrive[pt][tid] = true;
					this.arrive_tasks[pt][ ++this.arrive_tasks[pt][0] ] = tid;
					//System.out.println("\t " +pt+" -> "+tid);
				}
			}
		}
		//	使得arrive_tasks每一行各个任务按照拓扑结构排序，排名越靠前越先被访问
		int temp;
		int L;
		for(int i=0;i<this.task_num;i++) {
			L = this.arrive_tasks[i][0];
			for(int j=1;j<=L/2;j++) {
				temp = this.arrive_tasks[i][j];
				this.arrive_tasks[i][j] = this.arrive_tasks[i][L-j+1];
				this.arrive_tasks[i][L-j+1] = temp;
			}
		}
		
		//初始化pass_tasks,task_level_from_exit
		Arrays.fill(task_level_from_entry, 0);
		
		boolean can_pass[][] = new boolean [this.task_num][this.task_num];  //can_pass[i][j] 自entry_task抵达i是否可以途径j
		int remaining_in_edge_num[] = new int [this.task_num];
		for(int i=0;i<this.task_num;i++) { //设置remaining_in_edge_num默认值
			remaining_in_edge_num[i] = this.parent_tasks_id.get(i).size();
			this.pass_tasks[i][0] = 0;
			for(int j=0;j<this.task_num;j++) {
				can_pass[i][j] = false;
			}
		}
		//	自entry_task开始，遍历整个DAG
		//this.task_level_from_entry[this.entry_task_id] = 1;
		stack[0] = 1;
		stack[1] = this.entry_task_id;
		while(stack[0]!=0) {
			//出栈
			int tid = stack[ stack[0]-- ];
			//System.out.println("pull " + tid);
			ArrayList<Integer> children = this.child_tasks_id.get(tid);
			for(int i=0;i<children.size();i++) {
				int ct = children.get(i); //tid的子任务
				this.task_level_from_entry[ct] = Math.max(this.task_level_from_entry[tid]+1, this.task_level_from_entry[ct]);
				//更新remaining_in_edge_num,降为0则压栈
				if(--remaining_in_edge_num[ct]==0) {
					stack[ ++stack[0] ] = ct; //压栈
					//System.out.println("\t push "+pt);
				}
				//提取tid的pass_tasks
				for(int j=1;j<=this.pass_tasks[tid][0];j++) {
					int pt = this.pass_tasks[tid][j]; //tid的pass_task
					if(can_pass[ct][pt]==false) {
						can_pass[ct][pt] = true;
						this.pass_tasks[ct][ ++this.pass_tasks[ct][0] ] = pt;
						//System.out.println("\t " +pt+" --> "+ct);
					}
				}
				//更新can_pass[ct][tid],tid压入this.pass_tasks[ct]
				if(can_pass[ct][tid]==false) {
					can_pass[ct][tid] = true;
					this.pass_tasks[ct][ ++this.pass_tasks[ct][0] ] = tid;
					//System.out.println("\t " +pt+" -> "+tid);
				}
			}
		}
	}
	
	//从完成任务t1到任务t2开始经历的最短时间(假定每条边传输时间都是0,所有机器各用一台最快机器)
	private double min_wait_time(int t1,int t2) {
		double assumed_st[] = new double[this.task_num]; //假定每条边传输时间都是0,所有机器各用一台最快机器, 每个任务的开始时间
		double assumed_ft[] = new double[this.task_num]; //假定每条边传输时间都是0,所有机器各用一台最快机器, 每个任务的结束时间
		Arrays.fill(assumed_st, 0.0);
		Arrays.fill(assumed_ft, 0.0);
		for(int j=1;j<=this.arrive_tasks[t1][0];j++){
			int ct = this.arrive_tasks[t1][j];
			if(this.can_arrive[ct][t2]||ct==t2) {
				for(int pt:this.parent_tasks_id.get(ct)) {
					assumed_st[ct] = Math.max(assumed_st[ct], assumed_ft[pt]);
				}
				assumed_ft[ct] = assumed_st[ct] + this.TaskArray[ct].getTaskSize()/get_fastest_VM_speed();
			}
			if(ct==t2) {
				break;
			}
		}
		
		return assumed_st[t2] ;
		
	}
	//返回最快机器速度
	private double get_fastest_VM_speed() {
		return VM.SPEEDS[this.vm_types_speed_descend[0]];
	}
	//删除无用边,更新child_tasks_id,parent_tasks_id,is_child
	private void delete_unnecessary_edge() {
		for(int t=0;t<this.task_num;t++) {
			for(int j=1;j<=this.arrive_tasks[t][0];j++){
				int ct = this.arrive_tasks[t][j];
				if(
						this.task_level_from_entry[ct]-this.task_level_from_entry[t]>1 && 
						this.task_level_from_exit[t]-this.task_level_from_exit[ct]>1 && 
						this.is_child[t][ct] &&
						min_wait_time(t,ct) > this.TransRequireTime[t][ct] + tiny_num
						) {
					/*
					System.out.println("unnecessary_edge : "+t+"->"+ct);
					System.out.println("\t min_wait_time:" + min_wait_time(t,ct));
					System.out.println("\t TransRequireTime:" + this.TransRequireTime[t][ct]);
					*/
					
					//更新this.child_tasks_id
					ArrayList<Integer> cts = this.child_tasks_id.get(t);
					for(int i=0;i<cts.size();i++) {
						if(cts.get(i)==ct) {
							cts.set(i, cts.get(cts.size()-1));
							cts.remove(cts.size()-1);
							break;
						}
					}
					//更新this.parent_tasks_id
					ArrayList<Integer> pts = this.parent_tasks_id.get(ct);
					for(int i=0;i<pts.size();i++) {
						if(pts.get(i)==t) {
							pts.set(i, pts.get(pts.size()-1));
							pts.remove(pts.size()-1);
							break;
						}
					}
					//更新this.is_child[t][ct]
					this.is_child[t][ct] = false;
					if(t!=this.entry_task_id && ct!=this.exit_task_id) {
						if(is_print_information) System.out.println("delete edge "+t+"->"+ct);
					}

				}
			}
		}
		cal_arrive_and_level();//重新计算 arrive信息
		if(is_print_information) System.out.println("end delete_unnecessary_edge");
	}
	
	//解信息副本
	class copy_sol {
		private double cost = Double.MAX_VALUE; //完成调度后,实际使用的budget
		private double makespan = Double.MAX_VALUE; //完成调度时间
		private boolean feasiblity = false;
		private VM VM_Array[]; //所有被使用的机器按照其id存放在VM_Array中
		private int Vm_of_task[]; //每个任务被分配的机器
		private int Tasks_of_vm[][]; //每个vm执行的所有task,Tasks_of_vm[i][0]表示使用第i个机器的任务数，Tasks_of_vm[i][1]开始按照start_time由小到大罗列任务
		private int execute_rank_on_its_vm[];//每个任务在其占用机器上是第几个被执行的任务，也就是该任务在Tasks_of_vm的列号
		private int used_vm_num = 0; //使用的vm个数,即正在被占用的VM机器数目
		private double start_time[] ; //start_time[i]表示第i个任务的开始时间
		private double finish_time[] = null; //finish_time[i]表示第i个任务的完成时间
		private double execute_time[]; //执行时间, execute_time[i] = finish_time[i] - start_time[i]
		//private ArrayList<Integer> task_sort_list = null;
		
		public copy_sol() {
			mallocs();
		}
		
		public copy_sol(PACP_HEFT s) {
			mallocs();
			copy_inf(s);
		}
		
		public copy_sol(copy_sol s) {
			mallocs();
			copy_inf(s);
		}
		
		//数组申请空间
		private void mallocs() {
			cost = Double.MAX_VALUE; //完成调度后,实际使用的budget
			makespan = Double.MAX_VALUE; //完成调度时间
			feasiblity = false;
			this.VM_Array = new VM[2*task_num];
			this.Vm_of_task = new int[task_num]; //每个任务被分配的机器
			this.start_time = new double[task_num]; //finish_time[i]表示第i个任务的完成时间
			this.finish_time = new double[task_num]; //finish_time[i]表示第i个任务的完成时间
			this.execute_time = new double[task_num];//执行时间
			this.Tasks_of_vm = new int[2*task_num][task_num+1]; //每个vm执行的所有task
			this.execute_rank_on_its_vm = new int[task_num]; //每个任务被分配的机器
		}
		
		//复制PACP_HEFT信息
		private void copy_inf(PACP_HEFT s) {
			this.cost = s.cost;
			this.makespan = s.makespan;
			this.feasiblity = s.feasiblity;
			this.used_vm_num = s.used_vm_num;
			//复制各个成员信息
			for(int t=0;t<s.task_num;t++) {
				this.Vm_of_task[t] = s.Vm_of_task[t];
				this.start_time[t] = s.start_time[t];
				this.finish_time[t] = s.finish_time[t];
				this.execute_time[t] = s.execute_time[t];
				this.execute_rank_on_its_vm[t] = s.execute_rank_on_its_vm[t];
			}
			//复制VM_Array
			for(int i=0;i<s.used_vm_num;i++) {
				this.VM_Array[i] = new VM(s.VM_Array[i].getType());
			}
			//复制Tasks_of_vm
			for(int t1=0;t1<task_num;t1++) {
				for(int t2=0;t2<=task_num;t2++) {
					this.Tasks_of_vm[t1][t2] = s.Tasks_of_vm[t1][t2];
				}
			}
			//task_sort_list
			//this.task_sort_list = new ArrayList<Integer>(s.task_sort_list);
		}
		
		//复制copy_sol信息
		private void copy_inf(copy_sol s) {
			this.cost = s.cost;
			this.makespan = s.makespan;
			this.feasiblity = s.feasiblity;
			this.used_vm_num = s.used_vm_num;
			//复制各个成员信息
			for(int t=0;t<task_num;t++) {
				this.Vm_of_task[t] = s.Vm_of_task[t];
				this.start_time[t] = s.start_time[t];
				this.finish_time[t] = s.finish_time[t];
				this.execute_time[t] = s.execute_time[t];
				this.execute_rank_on_its_vm[t] = s.execute_rank_on_its_vm[t];
			}
			//复制VM_Array
			for(int i=0;i<s.used_vm_num;i++) {
				this.VM_Array[i] = new VM(s.VM_Array[i].getType());
			}
			//复制Tasks_of_vm
			for(int t1=0;t1<task_num;t1++) {
				for(int t2=0;t2<=task_num;t2++) {
					this.Tasks_of_vm[t1][t2] = s.Tasks_of_vm[t1][t2];
				}
			}
			//task_sort_list
			//this.task_sort_list = new ArrayList<Integer>(s.task_sort_list);
		}
	}
}
