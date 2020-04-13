#include <iostream>
#include <algorithm>
#include <cmath>
#include <vector>
#include <assert.h>

using namespace std;

const double eps=1e-6;

typedef vector<vector<double> > matrix;

vector<double> mul(vector<double> a,matrix& b){
    vector<double> c(a.size(),0);
    for (int i=0;i<1;i++)
    {
        for (int j=0;j<b[0].size();j++)
        {
            for (int k=0;k<b.size();k++)
                c[j]+=a[k]*b[k][j];
        }
    }
    return c;
}

vector<double> mul(matrix& b,vector<double> a){
    vector<double> c(a.size(),0);
    for (int i=0;i<b.size();i++)
    {
        for (int j=0;j<1;j++)
        {
            for (int k=0;k<a.size();k++)
                c[i]+=b[i][k]*a[k];
        }
    }
    return c;
}

pair<double,double> kek(double a,double b,double c,double d,double e,double f)
{
    return {(c*e-b*f)/(a*e-b*d),(a*f-c*d)/(a*e-b*d)};
}

class task
{
private:
    matrix a;
    vector<double> c;
    vector<int> perm;
    int vars,eqs;

    void find_nonzero(int I,int J,int& i,int& j,matrix& V)
    {
        for (int y=J; y<vars; y++)
            for (int x=I; x<eqs; x++)
                if (abs(V[x][y])>eps)
                {
                    i=x;
                    j=y;
                    return;
                }
    }

    void swap_column(int x,int y)
    {
        if (x==y)
            return;
        swap(perm[x],perm[y]);
        for (int i=0; i<eqs; i++)
            swap(a[i][x],a[i][y]);
        swap(c[x],c[y]);
    }

    void subtract_rows(int a,int b,double c,matrix& V) //a-=b*c
    {
        assert(a!=b);
        for (int j=0; j<V[a].size(); j++)
            V[a][j]-=V[b][j]*c;
    }
    void gauss(matrix& V)
    {
        for (int i=0; i<V.size(); i++)
        {
            int li=-1,lj=-1;
            find_nonzero(i,i,li,lj,V);
            if (li==-1)
            {
                throw new invalid_argument("!!!");
            }
            swap(V[i],V[li]);
            swap_column(i,lj);
            double t=V[i][i];
            for (int j=i; j<V[i].size(); j++)
            {
                V[i][j]/=t;
            }
            for (int j=i+1; j<eqs; j++)
            {
                subtract_rows(j,i,V[j][i],V);
            }
        }
        for (int j=eqs-2; j>=0; j--)
        {
            for (int k=eqs-1; k>j; k--)
            {
                subtract_rows(j,k,V[j][k],V);
            }
        }
    }

    matrix Binv()
    {
        matrix B(eqs);
        for (int i=0; i<eqs; i++)
        {
            B[i]=vector<double>(a[i].begin(),a[i].begin()+eqs);
            for (int j=0; j<eqs; j++)
            {
                B[i].push_back(i==j);
            }
        }
        gauss(B);
        for (int i=0;i<eqs;i++){
            B[i]=vector<double>(B[i].begin()+eqs,B[i].begin()+2*eqs);
        }

        return B;
    }

    vector<double> b_(){
        vector<double> b(eqs);
        for (int i=0;i<eqs;i++)
            b[i]=a[i].back();
        return b;
    }

public:
    task(initializer_list<vector<double> > l,initializer_list<double> l2):a(l),c(l2)
    {
        const double M=-1e9;
        eqs=a.size();
        for (int i=0;i<eqs;i++){
            for (int j=0;j<eqs;j++){
                a[i].push_back(i==j);
            }
            rotate(a[i].begin(),a[i].end()-eqs,a[i].end());
            c.push_back(M);
        }
        rotate(c.begin(),c.end()-eqs,c.end());
        vars=c.size();
        perm.resize(vars);
        for (int i=0; i<vars; i++)
            perm[i]=i;
        rotate(perm.begin(),perm.end()-eqs,perm.end());
    }


    void print(matrix& v,ostream& os=cout)
    {
        os << "[" << endl;
        for (auto &row:v)
        {
            os << "   [";
            for (auto x:row)
                os << x << ", ";
            os << "]," << endl;
        }
        os << "]" << endl;
    }

    template<typename T>
    void print(vector<T> v,ostream& os=cout)
    {
        os << "[";
        for (auto &x:v)
        {
            os << x << ", ";
        }
        os << "]" << endl;
    }
    auto basis()
    {
        vector<double> b(eqs,0);
        for (int i=0; i<eqs; i++)
            b[i]=a[i].back();
        return b;
    }


    vector<double> getX(double& f){
        auto t=a;
        gauss(a);
        f=0;
        vector<double> X(vars,0);
        for (int i=0;i<eqs;i++){
            X[i]=a[i].back();
            f+=X[i]*c[i];
        }
        a=t;
        return X;
    }

    void solve()
    {
        print(a);
        double f;
        print(getX(f));
        cout << f << endl;

        auto b=basis();
        int step=0;
        while(1)
        {
            cout << "step " << ++step << "=========" << endl;
            auto Bi=Binv();
            auto pi=mul(vector<double>(c.begin(),c.begin()+eqs),Bi);

            vector<double> d(vars-eqs,0);
            for (int i=eqs;i<vars;i++){
                for (int j=0;j<eqs;j++){
                    d[i-eqs]+=pi[j]*a[j][i];
                }
                d[i-eqs]-=c[i];
            }

            cout << "d = ";
            print(d);

            int q=min_element(d.begin(),d.end())-d.begin();

            if (d[q]>-eps){
                cout << "solution:" << endl;
                vector<pair<int,double> > v(vars);
                double f;
                auto X=getX(f);
                for (int i=0;i<vars;i++){
                    v[i]={perm[i],X[i]};
                }
                sort(v.begin(),v.end());
                for (auto x:v)
                    cout << "x [" << x.first+1 << "] = " << x.second << endl;
                cout << endl;
                cout << f << endl;
                break;
            }

            cout << "q = " << eqs+q+1 << endl;

            vector<double> aq(eqs);
            for (int i=0;i<eqs;i++)
                aq[i]=a[i][q+eqs];

            aq=mul(Bi,aq);

            vector<double> beta=mul(Bi,b_());
            int p=-1;
            for (int i=0;i<eqs;i++){
                if (aq[i]>eps)
                    if (p==-1||beta[i]/aq[i]<beta[p]/aq[p])
                        p=i;
            }
            if (p==-1){
                cout << "unlimited" << endl;
                return;
            }
            cout << "p = " << perm[p]+1 << endl;

            swap_column(p,q+eqs);

            print(a);
            print(getX(f));
            cout << f << endl;

            cout << endl;
        }

    }

};

int main()
{
    task A(
    {
        {2,-3,0,1,15},
        {2,5,7,1,44},
    },
        {2,1,0,-4}
    );
    A.solve();

    return 0;
}
