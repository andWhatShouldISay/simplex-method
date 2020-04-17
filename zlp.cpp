#include <iostream>
#include <algorithm>
#include <cmath>
#include <vector>
#include <assert.h>
#include <set>

using namespace std;

const double eps=1e-6;

typedef vector<vector<double> > matrix;

vector<double> mul(vector<double> a,matrix& b)
{
    vector<double> c(a.size(),0);
    for (int i=0; i<1; i++)
    {
        for (int j=0; j<b[0].size(); j++)
        {
            for (int k=0; k<b.size(); k++)
                c[j]+=a[k]*b[k][j];
        }
    }
    return c;
}

vector<double> mul(matrix& b,vector<double> a)
{
    vector<double> c(a.size(),0);
    for (int i=0; i<b.size(); i++)
    {
        for (int j=0; j<1; j++)
        {
            for (int k=0; k<a.size(); k++)
                c[i]+=b[i][k]*a[k];
        }
    }
    return c;
}

struct result
{
    vector<vector<double> > A;
    vector<double> c;

    result(vector<vector<double> > A,vector<double> c):A(A),c(c),f(0) {}

    vector<double> res;
    double f;
    int k;

    void print(bool all=true)
    {
        cout << "task " << k << ":" << endl;
        cout << "A = [" << endl;
        for (auto &row:A)
        {
            cout << "   [";
            for (auto x:row)
                cout << x << ", ";
            cout << "]," << endl;
        }
        cout << "]" << endl;
        cout << "c = [";
        for (auto &x:c)
        {
            cout << x << ", ";
        }
        cout << "]" << endl;
        if (!all)
            return;
        cout << "res = [";
        for (auto &x:res)
        {
            cout << x << ", ";
        }
        cout << "]" << endl;
        cout << f << endl;
        cout << endl;

    }

};

bool operator<(const result& A,const result& B)
{
    if (A.f!=B.f)
        return A.f>B.f;
    if (A.A!=B.A)
        return A.A<B.A;
    return A.c<B.c;
}

class task
{
private:
    result R;
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
                throw new invalid_argument("degenerate matrix");
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
        for (int i=0; i<eqs; i++)
        {
            B[i]=vector<double>(B[i].begin()+eqs,B[i].begin()+2*eqs);
        }

        return B;
    }

    vector<double> b_()
    {
        vector<double> b(eqs);
        for (int i=0; i<eqs; i++)
            b[i]=a[i].back();
        return b;
    }

    vector<double> getX(double& f)
    {
        auto t=a;
        gauss(a);
        f=0;
        vector<double> X(vars,0);
        for (int i=0; i<eqs; i++)
        {
            X[i]=a[i].back();
            f+=X[i]*c[i];
        }
        a=t;
        return X;
    }

    auto basis()
    {
        vector<double> b(eqs,0);
        for (int i=0; i<eqs; i++)
            b[i]=a[i].back();
        return b;
    }

public:
    task(vector<vector<double> > v,vector<double> v1):a(v),c(v1),R(v,v1)
    {
        const double M=-1e9;
        eqs=a.size();
        for (int i=0; i<eqs; i++)
        {
            for (int j=0; j<eqs; j++)
            {
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
        for (int i=0; i<eqs; i++)
            assert(vars+1==a[i].size());
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



    result solve()
    {
        auto b=basis();
        while(1)
        {
            auto Bi=Binv();
            auto pi=mul(vector<double>(c.begin(),c.begin()+eqs),Bi);

            vector<double> d(vars-eqs,0);
            for (int i=eqs; i<vars; i++)
            {
                for (int j=0; j<eqs; j++)
                {
                    d[i-eqs]+=pi[j]*a[j][i];
                }
                d[i-eqs]-=c[i];
            }


            int q=min_element(d.begin(),d.end())-d.begin();

            if (d[q]>-eps)
            {
                vector<pair<int,double> > v(vars);
                double f;
                auto X=getX(f);
                for (int i=0; i<vars; i++)
                {
                    v[i]= {perm[i],X[i]};
                }
                sort(v.begin(),v.end());
                vector<double> ans(vars);
                for (auto x:v)
                {
                    ans[x.first]=x.second;
                }
                for (int i=vars-eqs; i<vars; i++)
                    if (abs(ans[i])>1e-6)
                        throw invalid_argument("incompatible problem");

                ans.resize(vars-eqs);
                R.res=ans;
                R.f=f;
                return R;
            }


            vector<double> aq(eqs);
            for (int i=0; i<eqs; i++)
                aq[i]=a[i][q+eqs];

            aq=mul(Bi,aq);

            vector<double> beta=mul(Bi,b_());
            int p=-1;
            for (int i=0; i<eqs; i++)
            {
                if (aq[i]>eps)
                    if (p==-1||beta[i]/aq[i]<beta[p]/aq[p])
                        p=i;
            }
            if (p==-1)
            {
                throw new invalid_argument("umlimited");
            }

            swap_column(p,q+eqs);

        }
    }

};

bool isZ(double x)
{
    return abs(x-round(x))<1e-9;
}

bool isZ(vector<double>& v)
{
    for (auto x:v)
        if (!isZ(x))
            return false;
    return true;
}

bool cmp_Z(double a,double b)
{
    return (isZ(a)?1:a-floor(a))<(isZ(b)?1:b-floor(b));
}

int n;

result lim_floor(result R)
{
    int pos=min_element(R.res.begin(),R.res.begin()+n,cmp_Z)-R.res.begin();
    int x=floor(R.res[pos]);
    R.c.push_back(0);
    for (int i=0; i<R.A.size(); i++)
    {
        double t=R.A[i].back();
        R.A[i].pop_back();
        R.A[i].push_back(0);
        R.A[i].push_back(t);
    }
    vector<double> eq(R.c.size()+1,0);
    eq.back()=x;
    eq[pos]=1;
    eq[R.c.size()-1]=1;
    R.A.push_back(eq);
    R.k=2*R.k+1;
    return R;
}

result lim_ceil(result R)
{
    int pos=min_element(R.res.begin(),R.res.begin()+n,cmp_Z)-R.res.begin();
    int x=ceil(R.res[pos]);
    R.c.push_back(0);
    for (int i=0; i<R.A.size(); i++)
    {
        double t=R.A[i].back();
        R.A[i].pop_back();
        R.A[i].push_back(0);
        R.A[i].push_back(t);
    }
    vector<double> eq(R.c.size()+1,0);
    eq.back()=x;
    eq[pos]=1;
    eq[R.c.size()-1]=-1;
    R.A.push_back(eq);
    R.k=2*R.k+2;
    return R;
}

void go(result R,set<result>& s,result& ans)
{
    try
    {
        task t(R.A,R.c);
        int k=R.k;
        R=t.solve();
        R.k=k;
        R.print();
        if (isZ(R.res))
        {
            if(ans.res.empty()||R<ans){
                ans=R;
                cout << "currently optimal" << endl;
                cout << "============" << endl;
                cout << endl;
            } else {
                cout << "ignored" << endl;
                cout << "============" << endl;
                cout << endl;
            }
        }
        else
        {
            if (ans.res.empty()||R<ans){
                s.insert(R);
                cout << "will be branched" << endl;
                cout << "============" << endl;
                cout << endl;
            }   else {
                cout << "ignored" << endl;
                cout << "============" << endl;
                cout << endl;
            }
        }
    }
    catch (invalid_argument i)
    {
        R.print(0);
        cout << i.what() << endl;
        cout << "============" << endl;
        cout << endl;
        return;
    }
}

result solve(vector<vector<double> > A, vector<double> c)
{
    set<result> s;
    try
    {
        task t(A,c);
        auto r=t.solve();
        r.k=0;
        r.print();
        s.insert(r);

        if (isZ(r.res))
        {
            return r;
        }

        result ans({}, {});

        while(s.size())
        {
            auto R=*(s.begin());
            if (!ans.res.empty()&&R.f<ans.f){
                cout << "task " << R.k << " is ignored" << endl;
                cout << "============" << endl;
                cout << endl;
            }
            s.erase(s.begin());
            go(lim_floor(R),s,ans);
            go(lim_ceil(R),s,ans);
        }
        return ans;
    }
    catch(invalid_argument i)
    {
        cout << i.what () << endl;
    }
}

int main()
{
    vector<vector<double> > A=
    {
        {2,-3,0,1,15},
        {2,5,7,1,44},
    };
    n=A[0].size()-1;
    vector<double> c= {2,1,0,-4};
    auto p=solve(A,c);
    if (p.res.empty())
    {
        cout << "No solution";
    }
    else
    {
        p.res.resize(n);
        for (auto x:p.res)
            cout << x << ' ';
        cout << endl;
        cout << p.f << endl;
    }

    return 0;
}
