#导入flask
from flask import Flask,render_template,request,escape,url_for,jsonify
import cmath

import tkinter as tk
import time
import copy
import re

#用于将内部存储转换为子句输出
def convert_lang(clause_in):
    ret = ''
    for i in clause_in:
        if(clause_in.index(i)):
            ret += '|'
        if(i[1] == False):
            ret += '!'
        ret += i[0] + '(' + i[2] + ',' + i[3] + ')'
    if len(ret)==0:
        ret="None"
    return ret

#用于将输入子句转换为内部存储结构
def convert(str_in ):
    pattern = re.compile(r'([a-z]+\d+|[a-z]+)', re.I)   
    pattern1 = re.compile(r'(\|)')
    pattern2 = re.compile(r'(![a-z]+\(|[a-z]+\()', re.I) 
    m = pattern.findall(str_in)
    m1 = pattern1.findall(str_in)
    m2 = pattern2.findall(str_in)
    ret = []
    for i in range (len(m1) + 1):
        tmp = []
        for j in range (4):
            if(j==0 and m2[i][0]=='!'):
                tmp.append(False)
            elif(j==0):
                tmp.append(True)
            else:
                tmp.append(m[3*i+j-1])
        ret.append(tmp) 
    for i in ret:
        temp=i[0]
        i[0]=i[1]
        i[1]=temp   
    return ret

#合一函数，用于判断一阶逻辑子句是否能合一并输出所有的归结合一结果
def unify(clause_a,clause_b):
    subst=[]
    for a in clause_a:
        for b in clause_b:
            tmp=[]
            if(a[0]!=b[0]or a[1]==b[1]):
                continue
            elif(a[2]==b[2] and a[3]==b[3]):
                continue
            elif(a[2]!=b[2] and a[2][0]!='x' and b[2][0]!='x'):
                continue
            elif(a[3]!=b[3] and a[3][0]!='x' and b[3][0]!='x'):
                continue
            if(a[2]!=b[2]):
                if(a[2][0]=='x'):
                    tmp.append(a[2])
                    tmp.append(b[2])
                else:
                    tmp.append(b[2])
                    tmp.append(a[2])
            if(a[3]!=b[3]):
                if(a[3][0]=='x'):
                    tmp.append(a[3])
                    tmp.append(b[3])
                else:
                    tmp.append(b[3])
                    tmp.append(a[3])
            subst.append(tmp)


    clause_c=copy.deepcopy(clause_a)
    clause_d=copy.deepcopy(clause_b)
    ret=[]
    tmp=[]
    tmp.append(clause_c)
    tmp.append(clause_d)
    ret.append(tmp)
    for t in subst:
        tmp=[]
        clause_c=copy.deepcopy(clause_a)
        clause_d=copy.deepcopy(clause_b)
        for a in clause_c:
            if(len(t)>0):  
                if a[2]==t[0]: 
                    a[2]=t[1]
                if a[3]==t[0]: 
                    a[3]=t[1]
            if(len(t)>2):
                if a[2]==t[2]: 
                    a[2]=t[3]
                if a[3]==t[2]: 
                    a[3]=t[3]
        for a in clause_d: 
            if(len(t)>0):  
                if a[2]==t[0]: 
                    a[2]=t[1]
                if a[3]==t[0]: 
                    a[3]=t[1]
            if(len(t)>2):
                if a[2]==t[2]: 
                    a[2]=t[3]
                if a[3]==t[2]: 
                    a[3]=t[3]
        tmp.append(clause_c)
        tmp.append(clause_d)
        ret.append(tmp)   
    return ret

#归结函数主体实现，用于归结子句得出矛盾或者无法继续归结
def resolve(a,b):
    c=[]
    a_length=len(a)
    b_length=len(b)
    for i in range(0,a_length):
        for j in range(0,b_length):
            d=[]
            if(a[i][0]==b[j][0] and a[i][1]!=b[j][1] and a[i][2]==b[j][2] and a[i][3]==b[j][3]):
                if(a_length==1 and b_length>1):
                    for k in range(0,b_length):
                        if(k!=j):
                            d.append(b[k])
                    return d
                elif(a_length>1 and b_length==1):
                    for k in range(0,a_length):
                        if(k!=i):
                            d.append(a[k])
                    return d
                elif(a_length>1 and b_length>1):
                    a1=copy.deepcopy(a)
                    b1=copy.deepcopy(b)
                    del a1[i]
                    del b1[j]
                    for y in range(0,len(b1)):
                        d.append(b1[y])
                    for x in range(0,len(a1)):
                        T=0
                        for y in range(0,len(b1)):
                            if(a1[x][0]==b1[y][0] and a1[x][1]==b1[y][1] and a1[x][2]==b1[y][2] and a1[x][3]==b1[y][3]):
                                T=1
                        if(T==0):
                            d.append(a1[x])
                    return d
                elif(a_length==1 and b_length==1):
                    return d
    return False

#用于测试子句中是否含有变量
def test_variable(a,b):
    for t in a:
        if(t[2][0]=='x' or t[3][0]=='x'):
            return True
    for t in b:
        if(t[2][0]=='x' or t[3][0]=='x'):
            return True
    return False

#用于检测生成子句是否与已有重复
def exam(Horn,new):
    b=set()
    for tmp1 in new:
        b.add(tuple(tmp1))
    for a in Horn:
        c=set()
        for tmp1 in a.clause:
            c.add(tuple(tmp1))
        if c.issubset(b) :
            return False
    return True

#节点类，将归结过程显示更加有逻辑性
class Node:
    def __init__(self, clause, father,mother):
        self.clause = clause
        self.father = father
        self.mother = mother 

#创建一个app应用
#__name__指向程序所在的包
app=Flask(__name__)

#生成前端主页面
@app.route('/',methods=['GET','POST'])
def index1():
    return render_template("index.html")

#获取前端用户输入的子句集和归结目标
@app.route('/2',methods=['GET','POST'])
def index2():
    if request.method=='POST':
        #获取前端用户输入的子句集
        textarea1=request.form.get('textarea')
        text=textarea1.splitlines()
        #获取前端用户输入的归结目标
        input1=request.form.get('input')
        Horn=[]
        for i in range(0,len(text)-1):
                t=Node(convert(text[i]),0,0)
                Horn.append(t)
        target=convert(input1)
        target[0][1]=not target[0][1]
        t=Node(target,0,0)
        Horn.append(t)
        while True :
            t=len(Horn)
            NULL=False
            for tb_i in range(0,t):
                for tb_j in range(tb_i+1,t): 
                    new=unify(Horn[tb_i].clause,Horn[tb_j].clause)
                    for tt in new:
                        tmp=resolve(tt[0],tt[1])
                        if tmp==False:
                            continue
                        if  exam(Horn,tmp):
                            Horn.append(Node(tmp,tb_i+1,tb_j+1))
                        else:
                            continue
                        if len(tmp)==0:
                            NULL=True
                            break
                    if NULL:
                        break
                if NULL:
                    break
            if NULL:
                result=""
                for i in Horn:
                    result=result+convert_lang(i.clause)+"\n"
                    print(Horn.index(i)+1," ",convert_lang(i.clause),i.father,i.mother)
                print("归结成功")
                answer="归结成功"
                break
            if(t==len(Horn)):
                result=""
                for i in Horn:
                    result=result+convert_lang(i.clause)+"\n"
                    print(Horn.index(i)+1," ",convert_lang(i.clause),i.father,i.mother)
                print("归结失败")
                answer="归结失败"
                break


    return jsonify({'input':input1,'textarea':textarea1,'result':result,'answer':answer})

if __name__=='__main__':
    #web服务器的入口
    app.run(debug=True,port=5001)
