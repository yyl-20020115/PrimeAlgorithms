using System;
using System.ComponentModel.DataAnnotations;
using System.Numerics;

namespace Primes;


public class PrimesExperiment
{
    public const int RetryTimes = 20;

    public static readonly Random random = Random.Shared;

    public static BigInteger Fuse(BigInteger x, BigInteger c, BigInteger p)
        => ((x * x % p) + c) % p;

    public static BigInteger GetRandom(BigInteger a, BigInteger b)
    {
        var d = BigInteger.Abs(b - a);
        return GetRandom(d + 1) + BigInteger.Min(a, b);
    }
    public static BigInteger PollardRho(BigInteger x)
    {
        if (x == 4) return 2;
        var c = GetRandom(3, x - 1);//[3,x-1]
        var s = GetRandom(0, x - 1);//[0,x-1]
        s = Fuse(s, c, x);
        var t = Fuse(s, c, x);
        for (var lim = BigInteger.One; s != t; lim = BigInteger.Min(128, lim << 1))
        {
            var val = BigInteger.One;
            for (int i = 0; i < lim; ++i)
            {
                var tx = val * BigInteger.Abs(s - t) % x;
                if (tx == 0) break;
                val = tx;
                s = Fuse(s, c, x);
                t = Fuse(Fuse(t, c, x), c, x);
            }
            var d = BigInteger.GreatestCommonDivisor(val, x);
            if (d > 1) return d;
        }
        return x;
    }
    public static BigInteger Factor(BigInteger x, BigInteger max_factor)
    {
        if (x <= max_factor || x < 2) return max_factor;
        if (MillerRabin(x))
        {// x是质数
            if (x > max_factor)
            {
                max_factor = x;
            }
            return max_factor;
        }
        var p = x;
        while (p >= x) p = PollardRho(x);//找一个因子p
        while (x % p == 0) x /= p;
        max_factor = Factor(x, max_factor);
        max_factor = Factor(p, max_factor);
        return max_factor;
    }
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
    public static BigInteger GetRandomWith(int nbits)
    {
        //生成一个0到2^nbits-1的随机数
        if (nbits <= 0) return BigInteger.Zero;
        var bytes = new byte[(nbits + 7) / 8];
        random.NextBytes(bytes);
        bytes[^1] &= 0x7F; //确保最高位为0，避免负数
        return new(bytes);
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
    static BigInteger[][] Fibonacci2(BigInteger n)
    {
        var table = Array.Empty<BigInteger[]>();
        var n_copy = n;
        if (n_copy <= 1) return [[n_copy]];

        //斐波那契数列的分解
        //斐波那契数列的分解是一个贪心算法
        //从最大的斐波那契数开始，直到找到一个小于等于n的斐波那契数
        //然后将n减去这个斐波那契数，继续寻找下一个小于等于n的斐波那契数
        //直到n为0为止
        //首先给出一系列的盒子，每个盒子里放一个斐波那契数
        //
        var ranks = new List<BigInteger>();
        var square_ranks = new List<BigInteger>();
        var a = BigInteger.Zero;
        var b = BigInteger.One;
        var c = BigInteger.Zero;
        var d = BigInteger.Zero;
        ranks.Add(a);
        ranks.Add(b);
        square_ranks.Add(a);
        square_ranks.Add(b);
        var cc = BigInteger.Zero;
        while (cc < n_copy)
        {
            d = cc;
            c = a + b;
            ranks.Add(c);
            square_ranks.Add(cc = c * c);
            a = b;
            b = c;
        }
        var all_ranks = ranks.ToArray();
        //至此获得了所有的盒子和盒子的总数
        var all_square_ranks = square_ranks.ToArray();
        //将最终分解的结果装入列表
        var list = new List<BigInteger[]>
        {
            all_square_ranks[0..^1]
        };

        n_copy -= d;
        var i = square_ranks.Count - 1;
        for (; i >= 0; i--)
        {
            //计算需要的最小数量的盒子，盒子为斐波那契数列项目平方
            if (!n_copy.IsZero && n_copy >= square_ranks[i])
            {
                list.Add([.. square_ranks[0..(i + 1)]]);
                n_copy -= square_ranks[i];
                if (n_copy.IsZero) break;
            }
            if (i == 0)
            {
                i = square_ranks.Count - 1;
            }
        }
        list.Reverse();
        var counts = new List<(int count, BigInteger number)>();
        var dict = new Dictionary<BigInteger, int>();
        for (i = all_square_ranks.Length - 1; i >= 0; i--)
        {
            var key = all_square_ranks[i];
            var rows = list.Where(t => t[^1] == key).ToArray().Length;
            counts.Add((rows, key));
            if (key > BigInteger.One && rows > 0)
                dict[key] = rows;
        }
        //去掉结尾的1的数量。
        var agg = counts[..^2].Aggregate(BigInteger.Zero, (result, s) => result + s.count * s.number);
        if (agg != n)
        {
            throw new InvalidDataException($"Fibonacci decomposition failed: expected {n}, got {agg}");
        }

        //反转每一行
        for (i = 0; i < list.Count; i++)
        {
            list[i] = [.. list[i].Reverse()];
        }
        table = [.. list];
        //对反转后的表进行处理
        var sum = table.Aggregate(BigInteger.Zero, (result, row) => result + row[0]);
        if (sum != n)
        {
            throw new InvalidDataException($"Fibonacci decomposition failed: expected {n}, got {sum}");
        }
        return table;
    }
    /// <summary>
    /// 齐肯多夫定理（Zeckendorf's theorem）:
    /// ‌任何正整数均可唯一表示为若干个互不相邻的斐波那契数（通常排除首个斐波那契数1）之和。
    /// </summary>
    /// <param name="n"></param>
    /// <returns></returns>
    /// <exception cref="InvalidDataException"></exception>
    static BigInteger[][] Fibonacci(BigInteger n)
    {
        var table = Array.Empty<BigInteger[]>();
        var n_copy = n;
        if (n_copy <= 1) return [[n_copy]];

        //斐波那契数列的分解
        //斐波那契数列的分解是一个贪心算法
        //从最大的斐波那契数开始，直到找到一个小于等于n的斐波那契数
        //然后将n减去这个斐波那契数，继续寻找下一个小于等于n的斐波那契数
        //直到n为0为止
        //首先给出一系列的盒子，每个盒子里放一个斐波那契数
        //
        var ranks = new List<BigInteger>();
        var a = BigInteger.Zero;
        var b = BigInteger.One;
        var c = BigInteger.Zero;
        var d = BigInteger.Zero;
        ranks.Add(a);
        ranks.Add(b);
        while (c < n_copy)
        {
            d = c;
            ranks.Add(c = a + b);
            a = b;
            b = c;
        }
        //至此获得了所有的盒子和盒子的总数
        var all = ranks.ToArray();
        //将最终分解的结果装入列表
        var list = new List<BigInteger[]>
        {
            all[0..^1]
        };
        //减去最后的余数，因为用不上，因为余数可以被
        //已有的数列中的所有项目在单周期中处理。
        //这主要是因为斐波那契数列是致密的。
        //由于上限已经求出，且斐波那契数列是致密数列，
        //所以最终一定可以由斐波那契数列为基，实现唯一表述
        //正如算数基本定理（任何整数都有唯一分解形式），
        //任何整数都有唯一斐波那契数列分解的形式
        n_copy -= d;
        var i = ranks.Count - 1;
        for (; i >= 0; i--)
        {
            if (!n_copy.IsZero && n_copy >= ranks[i])
            {
                list.Add([.. ranks[0..(i + 1)]]);
                n_copy -= ranks[i];
                if (n_copy.IsZero) break;
            }
        }
        //此处的i可能大于0，说明有些数量并没有被使用
        if (i > 0)
        {
            //而这些未被使用的数量，在下面的统计过程中
            //也并未被计入
        }

        list.Reverse();
        var counts = new List<(int count, BigInteger number)>();
        var set = new HashSet<BigInteger>();
        //p的下限为i
        for (var p = all.Length - 1; p >= i; p--)
        {
            var key = all[p];
            //每一个都是唯一的，只有0和1两种可能
            var rows = list.Where(t => t[^1] == key).ToArray().Length;
            counts.Add((rows, key));
            if (key > BigInteger.One && rows > 0)
                set.Add(key);
        }
        counts.Reverse();
        var agg = counts.Aggregate(BigInteger.Zero, (result, s) => result + s.count * s.number);
        if (counts.All(c => c.count > 1))
        {
            throw new InvalidDataException("not possible");
        }
        if (agg != n)
        {
            throw new InvalidDataException($"Fibonacci decomposition failed: expected {n}, got {agg}");
        }
        //反转每一行
        for (i = 0; i < list.Count; i++)
        {
            list[i] = [.. list[i].Reverse()];
        }
        table = [.. list];
        //对反转后的表进行处理
        var sum = table.Aggregate(BigInteger.Zero, (result, row) => result + row[0]);
        if (sum != n)
        {
            throw new InvalidDataException($"Fibonacci decomposition failed: expected {n}, got {sum}");
        }
        return table;
    }

    static IEnumerable<BigInteger> NextFabonacci()
    {
        var fibonaccis = new List<BigInteger>() { BigInteger.One, BigInteger.One };
        yield return fibonaccis[0];
        yield return fibonaccis[1];

        while (true)
        {
            var next = fibonaccis[^1] + fibonaccis[^2];
            fibonaccis.Add(next);
            yield return next;
        }
    }


    static IEnumerable<BigInteger> NextPrime()
    {
        List<BigInteger> fibonaccis = [BigInteger.One, BigInteger.One];
        var last = fibonaccis.Aggregate(BigInteger.Zero, (result, f) => result + f);
        yield return last;
        while (true)
        {
            //生成下一个斐波那契数
            fibonaccis.Add(fibonaccis[^1] + fibonaccis[^2]);

            yield return last = NextPrimeWith(fibonaccis, last);
        }

        BigInteger NextPrimeWith(List<BigInteger> fibonaccis, BigInteger last)
        {
            var max = last << 1;
            var mask = FibonacciDecompose(last);
            while (true)
            {
                mask += 2;
                var value = GetFibonacciValueMask(fibonaccis,mask);
                if (value > max)
                {
                    throw new InvalidDataException($"Next prime exceeds max value: {max}");
                }
                else if (IsPrimeWithFibonaccis(fibonaccis, value))
                {
                    return value;
                }
            }
        }

        BigInteger GetFibonacciValueMask(List<BigInteger> fibonaccis, BigInteger mask)
        {
            var result = BigInteger.Zero;
            int i = 0;
            while (mask > 0)
            {
                //末尾为1(不是偶数，而是奇数，说明使用了这个斐波那契数)
                if (!mask.IsEven)
                {
                    result += fibonaccis[i];
                }
                mask >>= 1;
                i++;
            }

            return result;
        }
        
        void SetBit(byte[] bytes, int index, bool value)
        {
            ArgumentOutOfRangeException.ThrowIfGreaterThanOrEqual(index, bytes.Length * 8);
            var byteIndex = (int)(index / 8);
            var bitIndex = (int)(index % 8);
            if (value)
            {
                bytes[byteIndex] |= (byte)(1 << bitIndex);
            }
            else
            {
                bytes[byteIndex] &= (byte)~(1 << bitIndex);
            }
        }

        BigInteger FibonacciDecompose(BigInteger n)
        {           
            var n_copy = n;
            var ranks = new List<BigInteger>();
            var a = BigInteger.Zero;
            var b = BigInteger.One;
            var c = BigInteger.Zero;
            var d = BigInteger.Zero;
            ranks.Add(a);
            ranks.Add(b);
            while (c <= n_copy)
            {
                d = c;
                ranks.Add(c = a + b);
                a = b;
                b = c;
            }

            var bytes = new byte[(ranks.Count + 7) / 8 + 1];
            Array.Fill(bytes, (byte)0xFF);
            bytes[^1] &= (byte)(0xff >> (8 - ranks.Count % 8));
            //减去最后的余数，因为用不上，因为余数可以被
            //已有的数列中的所有项目在单周期中处理。
            //这主要是因为斐波那契数列是致密的。
            //由于上限已经求出，且斐波那契数列是致密数列，
            //所以最终一定可以由斐波那契数列为基，实现唯一表述
            //正如算数基本定理（任何整数都有唯一分解形式），
            //任何整数都有唯一斐波那契数列分解的形式
            var i = ranks.Count - 1;
            for (; i >= 0; i--)
            {
                if (!n_copy.IsZero && n_copy >= ranks[i])
                {
                    SetBit(bytes, i, true);
                    n_copy -= ranks[i];
                    if (n_copy.IsZero) break;
                }
            }
            //return bits as mask
            return new (bytes);
        }


        bool IsPrimeWithFibonaccis(List<BigInteger> fibonaccis, BigInteger sum, int start = 2)
        {
            if (sum <= 1) return false;
            if (sum == 2 || sum == 3) return true;
            if (sum.IsEven) return false;
            foreach (var f in fibonaccis[start..])
            {
                if (sum == f) continue;
                if (BigInteger.GreatestCommonDivisor(sum, f) > BigInteger.One)
                    return false;
            }
            //没有余数为0的，返回true说明是质数
            return true;
        }


        void GenerateCombinations(List<BigInteger> _fibonaccis, BigInteger min, BigInteger max, int bits, int start, List<BigInteger> current, HashSet<BigInteger> combinations)
        {
            if (_fibonaccis.Count <= 1) return;

            var p = _fibonaccis.FindLastIndex(f => f <= max);
            var fibonaccis = _fibonaccis[0..(p + 1)];

            // 生成组合：每一个fabonacci数都可以被选中或不选中,占1位
            var bytes = new byte[(fibonaccis.Count + 7) / 8 + 1];
            Array.Fill(bytes, (byte)0xFF);
            bytes[^1] &= (byte)(0xff >> (8 - fibonaccis.Count % 8));
            var template = new BigInteger(bytes);
            var index = template;

            bytes[^1] = 0;

            while (index > 2)
            {
                if (CountOnesOptimized(index) == bits)
                {
                    var sum = BigInteger.Zero;
                    for (int i = 0; i < fibonaccis.Count; i++)
                    {
                        if ((index & (BigInteger.One << i)) != 0)
                        {
                            sum += fibonaccis[i];
                        }
                    }
                    if (!sum.IsEven && sum >= min && sum <= max)
                    {
                        combinations.Add(sum);
                    }
                }

                index -= 2;
            }
        }
        int CountOnesOptimized(BigInteger n)
        {
            if (n <= ulong.MaxValue)
            {
                var u = (ulong)n;

                int count = 0;
                while (u > 0)
                {
                    count++;
                    u &= (u - 1); // 清除最低位的1
                }
                return count;
            }
            else
            {
                int count = 0;
                while (n > 0)
                {
                    count++;
                    n &= (n - 1); // 清除最低位的1
                }
                return count;
            }
        }
    }
    static int Main(string[] args)
    {
        if (false)
        {
            foreach (var f in NextFabonacci())
            {
                Console.WriteLine(f);
                if (f > 100) break;
            }
        }

        foreach (var p in NextPrime())
        {
            Console.WriteLine(p);
            if (!IsPrime(p))
            {
                Console.WriteLine($"Error: {p} is not prime!");
            }

            if (p > 1000) break;
        }

        for (int i = 100000; i >= 2; i--)
        {
            var b = GetRandomWith(2048);
            b = new BigInteger(i);
            var c = Fibonacci(b);

        }

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

            var n = BigInteger.Parse(line);

            if (MillerRabin(n))
            {
                Console.WriteLine("Yes, it's prime!");
            }
            else
            {
                Console.WriteLine("No, not prime.");

                var max_factor = BigInteger.One;
                max_factor = Factor(n, max_factor);
                if (n == max_factor) Console.Write("Prime\n");
                else Console.Write(max_factor);
            }
        }
        return 0;
    }
}
