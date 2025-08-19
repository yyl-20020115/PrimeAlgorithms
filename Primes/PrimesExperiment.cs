using System.Numerics;

namespace Primes;


public class PrimesExperiment
{
    public const int RetryTimes = 20;

    public static readonly Random random = Random.Shared;

    public static bool IsPrime(BigInteger n)
    {
        if (n < 2) return false;
        if (n == 2 || n == 3) return true;
        if (n % 2 == 0) return false; //排除偶数

        for (var i = 3; i * i <= n; i += 2)
        {
            if (n % i == 0) return false;
        }
        return true;
    }

    public static BigInteger MulMod(BigInteger a, BigInteger b, BigInteger mod)
    {//快速计算 (a*b) % mod
        var ans = BigInteger.Zero;
        while (b > 0)
        {
            if (!b.IsEven)
            {
                b--;
                ans = (ans + a) % mod;
            }
            b /= 2;
            a = (a + a) % mod;

        }
        return ans;
    }

    public static BigInteger PowMod(BigInteger a, BigInteger b, BigInteger mod)
    {//快速计算 (a^b) % mod
        var ans = BigInteger.One;
        while (!b.IsZero)
        {
            if (!b.IsEven)
            {
                ans = MulMod(ans, a, mod);
            }
            b /= 2;
            a = MulMod(a, a, mod);
        }
        return ans;
    }

    public static bool Verify(BigInteger a, BigInteger n)//miller_rabin算法的精华
    {//用检验算子a来检验n是不是素数
        var tem = n - 1;
        int j = 0;
        while (tem % 2 == 0)
        {
            tem /= 2;
            j++;
        }
        //将n-1拆分为a^r * s

        var x = PowMod(a, tem, n);
        //得到a^r mod n
        if (x == 1 || x == n - 1) return true;
        //余数为1则为素数
        while (j != 0) //否则试验条件2看是否有满足的 j
        {
            j--;
            x = MulMod(x, x, n);
            if (x == n - 1) return true;
        }
        return false;
    }

    public static BigInteger GetRandom(BigInteger n)
    {//生成一个0到n-1的随机数
        var data = n.ToByteArray();
        if (data.Length == 0)
            return BigInteger.Zero;

        BigInteger result;
        do
        {
            var bytes = new byte[data.Length];
            random.NextBytes(bytes);
            bytes[^1] &= 0x7F; //确保最高位为0，避免负数
            result = new BigInteger(bytes);
            result %= n;

        } while (result <= 0);
        return result;
    }
    public static bool MillerRabin(BigInteger n)
    {//检验n是否是素数
        if (n == 2 || n == 3)
            return true;
        if (n < 2 || n % 2 == 0)
            return false;
        //如果是2则是素数，如果<2或者是>2的偶数则不是素数

        for (int i = 1; i <= RetryTimes; i++)  //做times次随机检验
        {
            var a = GetRandom(n - 2) + 1;
            //得到随机检验算子 a
            if (!Verify(a, n))
                //用a检验n是否是素数
                return false;
        }
        return true;
    }
    static int Main(string[] args)
    {
        if (false)
        {
            for (var i = 0; i < 100000; i++)
            {
                var b1 = IsPrime(i);
                var b2 = MillerRabin(i);
                if (b1 != b2)
                {
                    Console.WriteLine($"Error at {i}: IsPrime={b1}, MillerRabin={b2}");
                }
            }
        }

        Console.WriteLine("Enter a number to check if it's prime (or type 'exit' to quit):");
        string? line;
        while (null != (line = Console.ReadLine()))
        {
            if (line.Trim().Equals("exit", StringComparison.CurrentCultureIgnoreCase))
                break;

            var tar = BigInteger.Parse(line);

            if (MillerRabin(tar))
                Console.WriteLine("Yes, it's prime!");
            else
                Console.WriteLine("No, not prime..");
        }
        return 0;
    }
}
