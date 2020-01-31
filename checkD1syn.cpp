#include <iostream>
#include <vector>
#include <list>
#include <fstream>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string>
#include <ctime>
#include <chrono>
#include <random>
#include <memory>
using namespace std;

// 根据token variable y的坐标y（i,j,t）产生它的DIMACS格式下的编号
// t是展开的步数，n是自动机的状态数，这里t从0开始
// i,j的范围都是从0到n-1
int tokenvarNo(int i, int j, int t, int n)
{
    return t*(n*n+1)+i*n+j+1;
}
// 根据坐标letter variable x的坐标x（t）产生它的DIMACS格式下的编号
// t是展开的步数，n是自动机的状态数，这里t是从1开始的。
int lettervarNo(int t, int n)
{
    //return t*n*n+1;
    return tokenvarNo(n-1,n-1,t-1,n)+1; // 相对于最后它前面的一个令牌变量的编号+1
}

// 同步变量-z变量，它们只用于D3同步检测中的同步约束条件的产生
// 它们的编号在所有轮展开完的令牌变量和字母变量的后面，
int zvarNo(int j,int t, int n)
{
    return t+n*n*(t+1)+j;
}
// 判断向量ls中是否含有 goal所代表的状态
// 参数向量ls实际上保存的是某个状态的全部前驱状态
bool isin(int goal, std::vector<int> ls)
{
    int i=0;
    for (; i<ls.size(); i++){
        if (goal==ls[i])
            return true;
    }

    if (i==ls.size())
        return false;
}

void computeClauseNum(std::vector<std::vector<int>>& in_a, std::vector<std::vector<int>>& in_b, int& clause_a, int& clause_b, int n)
{
    clause_a = 0, clause_b = 0;
    // 对每个（i,j)的对判断状态j的前驱的存在性
    for (int j=0; j<n; j++){
        if (in_a[j].size()>0 && in_b[j].size()>0){
            clause_a = clause_a + in_a[j].size()+1;
            clause_b = clause_b + in_b[j].size()+1;
        }
        else if (in_a[j].size()==0 && in_b[j].size()>0){ // 没有前驱
            clause_a = clause_a+1;  // a动作下的子句得到化简
            clause_b = clause_b + in_b[j].size()+1;
        }else if (in_a[j].size()>0 && in_b[j].size()==0){ // 有前驱
            clause_a = clause_a+in_a[j].size()+1;
            clause_b = clause_b+1;
        }else{ // 都为0的情况
            clause_b = clause_b+1; // 实际上会化简成一个，如果给a的子句加1，那么b的子句就不加了，这里是给b的子句加了
        }
    }
}

// filename 存放DIMACS的文件名，该文件是minisat求解器的输入
// in_a, in_b a和b动作下，每个状态对应的前驱状态
// n 自动机的状态数
// length是展开的深度（层次）
void generateD1synCNF(string filename, std::vector<std::vector<int>>& in_a, std::vector<std::vector<int>>& in_b, int n, int length)
{
    int clause_a = 0, clause_b = 0;

    computeClauseNum (in_a, in_b, clause_a, clause_b, n);

    ofstream file(filename); // DIMACS格式的公式写入in.txt文件中

    if (!file.is_open()) // 不能打开文件，报错
    {
        file << "unable to open  file of cnf formula:" << filename << endl;
    }
    else{
        int variables_no = n*n*(length+1)+length; // 计算变量的个数

        int clauses_no=n*n+length*n*(clause_a+clause_b)+n*n+1+(n*(n-1))/2;

        file<< "p cnf "  << variables_no << "  "<< clauses_no << endl; // DIMACS格式的第一句

        // 构造初始的子句集合C0
        file << "c begin to generate clause set C0"<< endl; // DIMACS文件开头是c，那么这句minisat求解器当它是注释
        // 以下产生的是初始时的y(i,j,0)
        for (int i=0; i<n; i++){
            for (int j=0; j<n; j++){
                if (i==j){ // 主对角线上取正的文字
                    file << "c y("<< i << "," << j  << "," << "0)"<<endl;
                    file << tokenvarNo(i,j,0,n) << " " << "0" << endl;
                }
                else{ // 其他位置上取否定的文字
                    file << "c !y("<< i << "," << j  << "," << "0)"<< endl;
                    file << "-" << tokenvarNo(i,j,0,n) << " "<< "0" << endl;
                }
            }
        }// 产生C0子句集合结束

        // 构造Ct变迁子句集合，t的取值范围是从1到length
        for (int t=1; t<= length; t++){ // propogate until reach the length
            file << "c begin to generate clause set from C1 to Cl"<< t << endl;
            for (int i=0; i<n; i++){  // 对每一对(i,j) 考虑
                for(int j=0; j<n; j++){
                    if (in_a[j].size()>0 && in_b[j].size()>0){ // 动作a是1边
                       ///////////开始产生a动作下的子句
                       file << "c y("<< i<<","<<j<<","<< t<<"), there are pre-images under action a"<<endl;
                       file << "c !y("<< i << "," << j  << "," <<t <<") or "<< "!x("<< t<<")";
                       for (int m=0; m<in_a[j].size(); m++){
                            file<<" or " << "y(" << i << ","<< in_a[j][m]<<","<< t-1 << ")";
                       }
                       file<< endl;

                       file<<"-"<<tokenvarNo(i, j, t, n)<<" "<<"-"<<lettervarNo(t,n)<<" "; // 产生公式（1.1）右边对应的子句
                       for (int m=0; m<in_a[j].size(); m++){
                            file<<tokenvarNo(i, in_a[j][m],t-1,n)<< " ";
                       }
                       file<<"0"<<endl;

                       for (int m=0; m<in_a[j].size(); m++){//产生公式（1.2）对应的子句
                            file << "c y("<< i << "," << j  << "," <<t <<") or "
                                   << "!x("<<t<<") or "
                                   << "!y("<< i << "," << in_a[j][m]  << "," <<t-1 <<")" << endl;

                            file<<tokenvarNo(i, j, t,n)<<" "
                                  <<"-"<<lettervarNo(t,n)<<" "
                                  <<"-"<<tokenvarNo(i, in_a[j][m],t-1,n)<< " "<<"0"<<endl;
                        }

                        //////////// 开始产生b动作的子句
                        file << "c y("<< i<<","<<j<<","<< t<<"), there are pre-images under action b"<<endl;
                        file << "c !y("<< i << "," << j  << "," <<t <<") or "<< "x("<<t<<")";
                        for (int m=0; m<in_b[j].size(); m++){
                            file << " or y("<< i << "," << in_b[j][m]  << "," <<t-1 <<")";
                        }
                        file<<endl;

                        file<<"-"<<tokenvarNo(i, j, t,n)<<" "<<lettervarNo(t,n)<<" "; // 产生公式（1.1）对应的左边的子句
                        for (int m=0; m<in_b[j].size(); m++){
                            file<<tokenvarNo(i, in_b[j][m],t-1,n)<< " ";
                        }
                        file<<"0"<<endl;

                        for (int m=0; m<in_b[j].size(); m++){ //产生公式（1.3）对应的子句
                            file << "c y("<< i << "," << j  << "," <<t <<") or "
                             << "x("<<t<<") or "
                             << "!y("<< i << "," << in_b[j][m]  << "," <<t-1 <<")" <<endl;

                            file<<tokenvarNo(i, j, t,n)<<" "
                            <<lettervarNo(t,n)<<" "
                            <<"-"<<tokenvarNo(i, in_b[j][m],t-1,n)<< " "<<"0"<<endl;
                        }

                    }else if (in_a[j].size()==0 && in_b[j].size()>0){ // a动作下，状态j没有前驱
                        ///////// a的动作下前驱没有 产生一个化简的子句
                        file << "c y("<< i<<","<<j<<","<< t<<"), no pre-images under action a"<<endl;
                        //file << "c !x("<<t<<")" << endl;
                        //file<<"-"<<lettervarNo(t,n)<<" " << "0" << endl;
                        // 修改为论文上的
                        file << "-" << tokenvarNo(i,j,t,n)<< " "<< "-"<< lettervarNo(t,n)<<" "<< "0" << endl;
                       //////////// 开始产生b动作的子句
                        file << "c y("<< i<<","<<j<<","<< t<<"), there are pre-images under action b"<<endl;
                        file << "c !y("<< i << "," << j  << "," <<t <<") or "<< "x("<<t<<")";
                        for (int m=0; m<in_b[j].size(); m++){
                            file << " or y("<< i << "," << in_b[j][m]  << "," <<t-1 <<")";
                        }
                        file<<endl;

                        file<<"-"<<tokenvarNo(i, j, t,n)<<" "<<lettervarNo(t,n)<<" "; // 产生公式（1.1）对应的左边的子句
                        for (int m=0; m<in_b[j].size(); m++){
                            file<<tokenvarNo(i, in_b[j][m],t-1,n)<< " ";
                        }
                        file<<"0"<<endl;

                        for (int m=0; m<in_b[j].size(); m++){ //产生公式（1.3）对应的子句
                            file << "c y("<< i << "," << j  << "," <<t <<") or "
                             << "x("<<t<<") or "
                             << "!y("<< i << "," << in_b[j][m]  << "," <<t-1 <<")" <<endl;

                            file<<tokenvarNo(i, j, t,n)<<" "
                            <<lettervarNo(t,n)<<" "
                            <<"-"<<tokenvarNo(i, in_b[j][m],t-1,n)<< " "<<"0"<<endl;
                        }
                    }else if (in_a[j].size()>0 && in_b[j].size()==0){
                        file << "c y("<< i<<","<<j<<","<< t<<"), no pre-images under action b"<<endl;
                        //file << "c x("<<t<<")" << endl;
                        //file <<lettervarNo(t,n)<<" " << "0" << endl;
                        // 修改为论文上的
                        file << "-" << tokenvarNo(i,j,t,n) << " " << lettervarNo(t,n) << " " << "0"<<endl;
                        ///////开始产生a动作下的子句
                        file << "c y("<< i<<","<<j<<","<< t<<"), there are pre-images under action a"<<endl;
                       file << "c !y("<< i << "," << j  << "," <<t <<") or "<< "!x("<< t<<")";
                       for (int m=0; m<in_a[j].size(); m++){
                            file<<" or " << "y(" << i << ","<< in_a[j][m]<<","<< t-1 << ")";
                       }
                       file<< endl;

                       file<<"-"<<tokenvarNo(i, j, t, n)<<" "<<"-"<<lettervarNo(t,n)<<" "; // 产生公式（1.1）右边对应的子句
                       for (int m=0; m<in_a[j].size(); m++){
                            file<<tokenvarNo(i, in_a[j][m],t-1,n)<< " ";
                       }
                       file<<"0"<<endl;

                       for (int m=0; m<in_a[j].size(); m++){//产生公式（1.2）对应的子句
                            file << "c y("<< i << "," << j  << "," <<t <<") or "
                                   << "!x("<<t<<") or "
                                   << "!y("<< i << "," << in_a[j][m]  << "," <<t-1 <<")" << endl;

                            file<<tokenvarNo(i, j, t,n)<<" "
                                  <<"-"<<lettervarNo(t,n)<<" "
                                  <<"-"<<tokenvarNo(i, in_a[j][m],t-1,n)<< " "<<"0"<<endl;
                        }
                    }else{ // a和b的动作下都没有前驱
                          file << "c y("<< i<<","<<j<<","<< t<<"), no pre-images under action a and b"<<endl;
                          file << "c !y("<< i<<","<<j<<","<< t<<")"<<endl;

                          file << "-" << tokenvarNo(i,j,t,n) << " 0" << endl;
                    }
                }// end for j
            }// end for i
        } // end for t 结束Ct产生

        // 构造公式（1.4）对应的子句集
        file << "c begin to generate（1.4）formula" << endl;
        for (int j=0; j<n; j++){
            for (int i=0; i<n; i++){
                file << "c !y("<< i << "," << j  << "," <<length <<") or "
                       << "y("<< (i+1)%n << "," << j  << "," <<length <<")"<< endl;
                file<<"-"<<tokenvarNo(i, j, length,n)<<" "<< tokenvarNo((i+1)%n,j,length,n) <<" "<<"0" << endl;

            }// end for
        }// end for 结束(1.4)产生

        // 构造公式（1.5）对应的子句集，只有1个子句，它有n个文字
        file << "c begin to generate（1.5）formula" << endl;
        file << "c ";
        for (int j=0; j<n-1; j++){
             file << "y("<< 0 << "," << j  << "," <<length <<") or ";
        }
        file <<"y("<< 0 << "," << n-1 << "," <<length <<")" << endl;

        for (int j=0; j<n; j++){
             file<<" "<< tokenvarNo(0,j,length,n);
        }
        file << " " << "0" << endl;// 结束产生（1.5）

        // 构造公式（1.6）对应的子句集,有 n(n-1)/2个子句
        file << "c begin to generate（1.6）formula" << endl;
        for (int j=0; j<n; j++){
            for (int k=0; k<n; k++){
                if (j<k){
                    file << "c !y("<< 0 << "," << j  << "," <<length <<") or "
                           << "!y("<< 0 << "," << k  << "," <<length <<")" << endl;
                    file<<"-"<<tokenvarNo(0, j, length,n)<<" "<<"-"<<tokenvarNo(0,k,length,n) <<" "<<"0" << endl;
                }
            }// end for
        }// end for
        file.close();
    }// end if
}

// low和high表示二分搜索的区间
// 返回最小值
int binarySearch(int low, int high, string filename, std::vector<std::vector<int>>& in_a, std::vector<std::vector<int>>&in_b, int n)
{
    string word;
    int minlenthsynword = high;
    ifstream inputfile;
    ofstream resultfile;
    resultfile.open("result.txt"); // 注意打开模式是追加写入

    while(low < high){ // 注意循环结束的条件
        int mid = (low+high)/2;
        // 产生新的公式
        generateD1synCNF(filename, in_a, in_b, n, mid); // 注意对应的修改

        //system("minisat in.txt out.txt");
        system("minisat in.txt out.txt -strict -cpu-lim=7200");

        if (resultfile.is_open())
        {
            inputfile.open("out.txt");
            inputfile >> word;
                if (word=="SAT"){
                    high=mid; // 上界缩小
                    minlenthsynword = mid; // 更新这个最小值
                    cout<<"sat with length = "<<mid<<endl;
                    resultfile<<"sat with length = "<<mid<<endl; // 最后一次SAT的长度就是最小值
                }else if (word=="UNSAT"){
                    low = mid+1; // 上界增大
                    cout<<"not sat with length = "<<mid<<endl;
                    resultfile<<"not sat with length = "<<mid<<endl;

                }
            inputfile.close();

        }else
            cout << "Unable to open out or result file.";
        // getchar(); 用于调试
    }// end while
    resultfile.close();
    return minlenthsynword;
}

void generateNFAUniformDistr(int n, std::vector<std::vector<int>>& in_a, std::vector<std::vector<int>>& in_b)
{
    const std::mt19937::result_type seed = std::random_device{}();
    std::mt19937 eng{seed};

    int imgbound = 2; // #image参数的界限，默认是n
    uniform_int_distribution<int> dist_uniform2(0,imgbound); //  变迁函数delta(q,a)得到的后继状态集大小可以能是0到n，在它上进行均匀选择

    int num_trans, image_pos, image;
    int para1; // 用来控制随机产生了多少个后继

    for(int ga=0;ga<=n-1;ga++) // 对于动作a，对n个状态中的每个状态，考虑这个动作的后继 for action a, save the image for state ga
    {

        std::vector<int> data;

        for (int i=0; i<n+1; i++){
            data.push_back(i);
        }

        num_trans = dist_uniform2(eng); // 确定动作a下的非确定的变迁有多少个后继，这个可能性是0，1，...，n 是等概率的
        // num_trans可以直接复制，确定的后继数
        para1 = n;
        for (int i=0; i<num_trans; i++){
            uniform_int_distribution<int> dist_uniform3(0,para1-1); //   for selection size of set of transitions delta(q,a)
            para1--;
            image_pos = dist_uniform3(eng); // 可以保证与前面取的不重复吗，不能保证。要一次性产生num_trans个状态作为后继的相
            in_a[data[image_pos]].push_back(ga);  // 反过来，保存前驱
            data.erase(data.begin()+image_pos);
        }

    }

        for(int gb=0;gb<=n-1;gb++) // 类似的，对于动作b
        {
            std::vector<int> data(n+1);
            data.clear();
            for (int i=0; i<n+1; i++){
                data.push_back(i);
            }
            num_trans = dist_uniform2(eng); // 确定动作b下的非确定的变迁有多少个后继，这个可能性是0，1，...，n 是等概率的
            para1 = n;
            for (int i=0; i<num_trans; i++){
                uniform_int_distribution<int> dist_uniform3(0,para1-1); //   for selection size of set of transitions delta(q,a)
                para1--;
                image_pos = dist_uniform3(eng); // 可以保证与前面取的不重复吗，不能保证。要一次性产生num_trans个状态作为后继的相
                in_b[data[image_pos]].push_back(gb);  // 反过来，保存前驱
                data.erase(data.begin()+image_pos);
            }
        }
}

int main()
{
    int n=10;   // 指定要产生的自动机的状态个数
    int length=40;      // length是公式要展开的深度，论文中取4*n，n*n
    int experimentNum = 100; // 实验次数
    ofstream result ("result.txt");
    ofstream report ("report.txt");

    if (result.is_open()){
        result <<"number of states = "<<n<<endl;
    }

    if (report.is_open()){
        report << "Test NFA, number of states = " << n << " propogating length = " << length << endl;
    }

    for (int i=1; i<=experimentNum; i++){
    // 对n个状态的自动机，保存随机产生的动作a和b的前驱状态集
    std::vector<std::vector<int>> in_a(n*n);
    std::vector<std::vector<int>> in_b(n*n);

    /////////////////////////////////////////// 产生自动机 /////////////////////////////
    //产生Pn自动机
    /*
    for(int ga=0;ga<=n-1;ga++) // 对于动作a，对n个状态中的每个状态，考虑这个动作的后继 for action a, save the image for state ga
    {
        if (ga == 0||ga ==1){
            in_a[ga+1].push_back(ga);
        }else{
            in_a[ga].push_back(ga);
        }
    }

    for(int gb=0;gb<=n-1;gb++) // 类似的，对于动作b
    {
        if (gb == 0){
            in_b[1].clear();
        }else if (gb == n-1){
            in_b[0].push_back(gb);
        }else{
            in_b[gb+1].push_back(gb);
        }
    }// 产生Pn自动机结束
    */
    /*
    //*产生论文上的例子
    in_a[1].push_back(0);
    in_b[0].push_back(0);
    in_b[0].push_back(1);
    in_b[1].push_back(1);
    //论文上的那个例子结束
    */
    generateNFAUniformDistr(n, in_a, in_b);
////////////////////////////////////////////////////////////////////
////////////////////////////////////////////// 产生CNF公式  ////////////////////
    generateD1synCNF("in.txt", in_a, in_b, n, length); // 注意产生什么类型的公式：D1，D2还是D3

    // 算法写出来 首先产生公式
    // 接着调用一次求解器，如果满足，转二分搜索
    // 如果不满足说明失败了，可能是展开的长度设置的比较小所致，也有可能是自动机本身就是不可同步的
    // invoke sat solver
    system("minisat in.txt out.txt -strict -cpu-lim=7200");

/////////binary search///////////////////////////
    string word;
    ifstream outfile;
    outfile.open("out.txt");

    int minresult=length;

    if (outfile.is_open())
    {
        outfile>>word;
        if (word=="SAT"){
            cout<<"sat with length = "<<length<<endl;
            result << "sat with length="<<length<< endl;
            // 开始进行二分法
            minresult = binarySearch(1,length,"in.txt", in_a, in_b, n);
            // 将这个值保存到文件report.txt
            report << "experiment No = " << i << ", SAT, shortest length = " << minresult << endl;
        }else if (word=="UNSAT"){
            cout << "not sat with length = "<<length<<endl;
            result << "not sat with length = "<<length<<endl;
            report << "experiment No = " << i << ", UNSAT, testing length = " << length << endl;
        }
        outfile.close();
    }else
        cout << "Unable to open out file.";

    result.close();
    } // end for
    return(0);
}
