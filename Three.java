import it.unisa.dia.gas.jpbc.*;
import it.unisa.dia.gas.plaf.jpbc.pairing.PairingFactory;
import java.lang.reflect.Proxy;
import java.lang.reflect.InvocationHandler;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.List;
import java.io.IOException;
import java.util.Random;
import java.io.BufferedReader;
import java.io.FileReader;
import java.util.HashSet;
import java.util.Set;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.nio.ByteBuffer;



interface Ident {
    void buildSystem();
    void extractSecretKey();
    void authenticator();
    void challenge();
    void prove();
    void verify();
    void HIC();
}

/**
 * 时间统计处理机，用于统计各方法耗时
 */
class TimeCountProxyHandle implements InvocationHandler {

    private final Object proxied;

    public TimeCountProxyHandle(Object obj) {
        proxied = obj;
    }

    @Override
    public Object invoke(Object proxy, Method method, Object[] args) throws Throwable {
        long begin = System.currentTimeMillis();
        Object result = method.invoke(proxied, args);
        long end = System.currentTimeMillis();
        System.out.println(method.getName() + "耗时:" + (end - begin) + "ms");
        return result;
    }
}

class BasicIdent2 implements Ident {
    private Element m_i, k, alpha_i, m_i_prime, hash_i_j, m_ij, r, h_ij, sigma_ij, sigma_i, tau0, H, M, sigmaii, v_i, lambda_j;
    private Element g1, u, x, g, msk, a, y, id, sk, gamma, sigma;
    private Element left1, right1, leftTerm1, leftTerm2, leftTerm3, RResult, LResult, e_sigma_g, term1, term2, term3;
    private Element v_I, H_I, H_II, v_II, Lambda;
    private Field G1,  G2, Zr;
    private Pairing pairing;

    List<Element> fileParts = new ArrayList<>();
    List<Element> sigma_ijList = new ArrayList<>(); // 存储每个 j 的签名
    List<Element> sigma_iList = new ArrayList<>(); // 存储每个 j 的签名
    List<Integer> iList = new ArrayList<>();
    List<Element> vList = new ArrayList<>();
    List<Element> lambdaList = new ArrayList<>(); // 用于存储 lambda_j
    List<Element> m_ijList = new ArrayList<>();
    List<Element> h_ijList = new ArrayList<>();

    public BasicIdent2() {
        init();
    }
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    private Element H1(String input) {
        // 示例实现: 使用域 Zq 的 SHA-256 散列
        // 实际实现时请替换此代码为适合您需求的哈希逻辑
        try {
            byte[] hashBytes = java.security.MessageDigest.getInstance("SHA-256").digest(input.getBytes());
            return Zr.newElementFromBytes(hashBytes).getImmutable();
        } catch (Exception e) {
            throw new RuntimeException("哈希计算失败: " + e.getMessage());
        }
    }

    private Element H(String input) {
        // 示例实现: 使用群G1 的 SHA-256 散列
        // 实际实现时请替换此代码为适合您需求的哈希逻辑
        try {
            byte[] hashBytes = java.security.MessageDigest.getInstance("SHA-256").digest(input.getBytes());
            return G1.newElementFromBytes(hashBytes).getImmutable();
        } catch (Exception e) {
            throw new RuntimeException("哈希计算失败: " + e.getMessage());
        }
    }

    public Element f(Element k, int i) {
        try {
            // 1. 将 k 转换为 Zq 的字节表示
            byte[] kBytes = k.toBytes();

            // 2. 将整数 i 转换为 4 字节数组（大端序）
            byte[] iBytes = ByteBuffer.allocate(4).putInt(i).array();

            // 3. 合并字节数组（添加分隔符避免歧义）
            // 示例分隔符：k长度(4字节) + kBytes + iBytes
            byte[] combined = new byte[4 + kBytes.length + 4 + iBytes.length];
            ByteBuffer buffer = ByteBuffer.wrap(combined)
                    .putInt(kBytes.length)  // 写入 k 字节长度
                    .put(kBytes)            // 写入 k 内容
                    .putInt(iBytes.length)  // 写入 i 字节长度
                    .put(iBytes);            // 写入 i 内容

            // 4. 使用 SHA-256 哈希
            MessageDigest md = MessageDigest.getInstance("SHA-256");
            byte[] hash = md.digest(combined);

            // 5. 将哈希值映射到 Zq（自动取模）
            return Zr.newElementFromBytes(hash).getImmutable();
        } catch (NoSuchAlgorithmException e) {
            throw new RuntimeException("SHA-256 不可用", e);
        }
    }
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////
    private void init() {
        pairing = PairingFactory.getPairing("a.properties");//
        PairingFactory.getInstance().setUsePBCWhenPossible(true);
        checkSymmetric(pairing);
        // 获取双线性配对的群和域
        G1 = pairing.getG1(); // 获取群 G1
        G2 = pairing.getG2(); // 获取群 G2
        Zr = pairing.getZr(); // 获取域 Zq

        g = G1.newRandomElement().getImmutable(); // 初始化 g 为 G1 的随机生成元
    }

    private void checkSymmetric(Pairing pairing) {
        if (!pairing.isSymmetric()) {
            throw new RuntimeException("密钥不对称!");
        }
    }

    /////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    @Override
    public void buildSystem() {
        System.out.println("-------------------系统建立阶段----------------------");
        a = Zr.newRandomElement().getImmutable();
        x = Zr.newRandomElement().getImmutable();
        u = G1.newRandomElement().getImmutable();
        g1 = G1.newRandomElement().getImmutable();
        y = g.powZn(x).getImmutable(); // 计算 g^x = y
        msk = g1.powZn(x).getImmutable();
    }

    @Override
    public void extractSecretKey() {
        System.out.println("-------------------密钥提取阶段----------------------");
        id = G1.newRandomElement().getImmutable(); // 随机数 id 属于 G1
        // 计算私钥 sk = (g1^x)(id^a)
        sk = g1.powZn(x).mul(id.powZn(a)).getImmutable();
        // 计算 gamma = g^a
        gamma = g.powZn(a).getImmutable(); // 计算 gamma
        // 验证双线性对等式 e(sk, g) = e(g2, y) * e(id, gamma)
        left1 = pairing.pairing(sk, g).getImmutable(); // 左侧：e(sk, g)
        right1 = pairing.pairing(g1, y).mul(pairing.pairing(id, gamma)).getImmutable(); // 右侧：e(g2, y) * e(id, gamma)

        // 输出计算结果
        System.out.println("随机数 id: " + id);
        System.out.println("私钥 sk: " + sk);
        System.out.println("随机数 a: " + a);
        System.out.println("gamma = g^a: " + gamma);
        System.out.println("左侧 (e(sk, g)): " + left1);
        System.out.println("右侧 (e(g2, y) * e(id, gamma)): " + right1);

        // 验证结果
        if (left1.isEqual(right1)) {
            System.out.println("验证成功: 双线性对等式成立。");
        } else {
            System.out.println("验证失败: 双线性对等式不成立。");
        }
    }
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    @Override
    public void authenticator() {
        System.out.println("-------------------标签生成阶段----------------------");
        // 读取数据文件
        String filename = "D:\\samrt_contract\\my_improve\\src\\123.txt"; // 确保提供正确的路径
        int n = 200;

        try (BufferedReader br = new BufferedReader(new FileReader(filename))) {
            StringBuilder contentBuilder = new StringBuilder();
            String line;
            // 读取文件内容并添加到字符串构建器中
            while ((line = br.readLine()) != null) {
                contentBuilder.append(line).append("\n"); // 每行后添加换行符
            }
            // 获取文件的完整内容
            String content = contentBuilder.toString();
            int totalLength = content.length();
            int chunkSize = (int) Math.ceil((double) totalLength / n); // 计算每个数据块的长度

            for (int i = 0; i < n; i++) {
                // 计算每个数据块的起止位置
                int start = i * chunkSize;
                int end = Math.min(start + chunkSize, totalLength); // 确保不超出总长度

                // 提取数据块并添加到列表
                if (start < totalLength) { // 确认起始位置在范围内
                    String m = content.substring(start, end).trim(); // 提取块并去除前后空白  字符串m
                    // 将每行数据转换为 Zq 中的元素
                    m_i = Zr.newElementFromBytes(m.getBytes()).getImmutable();
                    fileParts.add(m_i);  // 将块添加到列表中
                }
            }
            // 输出每个数据块
//            for (int i = 0; i < fileParts.size(); i++) {
//                System.out.println("m_" + (i + 1) + ":");
//                System.out.println(fileParts.get(i));
//                System.out.println(); // 添加空行与分隔
//            }
        } catch (IOException e) {
            System.out.println("读取文件出错: " + e.getMessage());
        }

        //盲化
        k = Zr.newRandomElement().getImmutable(); // 随机数 k 属于 Zq
        // 处理每一份数据
        for (int i = 0; i < n; i++) {
            m_i = fileParts.get(i); // 获取第 i 份数据
            if (i == 1 || i == 3) {
                alpha_i = f(k, i);
                m_i_prime = m_i.add(alpha_i).getImmutable(); // m_i' = m_i + alpha_i
                fileParts.set(i, m_i_prime); // 使用 m_i' 替换原始的 m_i
            }
        }

        //副本生成
        int N = 5;
        r = Zr.newRandomElement().getImmutable(); // 随机数 r 属于 Zq

        for (int i = 0; i < n; i++) {
            m_i = fileParts.get(i); // 原始数据块 m_i

            for (int j = 1; j <= N; j++) {
                // 计算副本 m_{ij} = m_i + H(filename || sk || i || j) mod q
                hash_i_j = H1(filename + sk.toString() + i + j); // H(filename || sk || i || j)
                m_ij = m_i.add(hash_i_j).getImmutable(); // 计算 m_{ij}
                m_ijList.add(m_ij);
//                System.out.println("副本 m_" + (i + 1) + j + ": " + m_ij);

                // 计算 h_{ij} = H(filename || i || j)
                h_ij = H(filename + i + j); // 计算 h_{ij}
                h_ijList.add(h_ij);

                // 计算 sigma_{ij} = sk * (h_{ij} * u^{(m_{ij})})^r
                sigma_ij = sk.mul((h_ij.mul(u.powZn(m_ij))).powZn(r)).getImmutable();
                // 将当前签名添加到列表
                sigma_ijList.add(sigma_ij);
                }

            // 计算最终的 sigma_i = sigma_{i1} · sigma_{i2} · ... · sigma_{iN}
            int startIdx = i * N; // 当前i对应的sigma_ij的起始索引
            sigma_i = sigma_ijList.get(startIdx); // 初始值为 sigma_{i1}
            for (int j = 1; j < N; j++) {
                sigma_i = sigma_i.mul(sigma_ijList.get(startIdx + j)).getImmutable(); // 累乘
            }
            sigma_iList.add(sigma_i);
//            System.out.println("最终签名 sigma_" + (i + 1) + ": " + sigma_i);
        }

        // 计算 tau0 = g^r
        tau0 = g.powZn(r).getImmutable(); // 计算 tau0
//        System.out.println("计算得到的 tau0: " + tau0); // 打印 tau0

        // 计算 H 和 M
        H = G1.newOneElement(); // H 的初始值为 1
        M = Zr.newZeroElement(); // M 的初始值为 0

        // 计算 H 和 M
        for (int i = 0; i < n; i++) { // 遍历每个 m_i
            for (int j = 1; j <= N; j++) { // 遍历每个副本 m_{ij}
                // 获取当前 h_{ij}
                Element h_ij = h_ijList.get((i * N) + (j - 1)); // 确保获取正确的 h_{ij}，索引计算
                H = H.mul(h_ij).getImmutable(); // H = H * h_{ij}

                // 获取当前 m_{ij}
                Element m_ij = m_ijList.get((i * N) + (j - 1)); // 确保获取正确的 m_{ij}，索引计算
                M = M.add(m_ij).getImmutable(); // M = M + m_{ij}
            }
        }

        // 将 M 对 q 取模
        //M = M.mod(q); // 可以在这里进行模 q 运算，即使 H, M 在此进行了更新

        // 计算双线性映射结果
        sigmaii = G1.newOneElement(); // 初始值为 1
        for (int i = 0; i < n; i++) {
            sigmaii = sigmaii.mul(sigma_iList.get(i)).getImmutable();
        }
        LResult = pairing.pairing(sigmaii, g).getImmutable();

        // 计算最终表达式 e(σ_i, g) = e(g_1, y)^(nN) * e(id, gamma)^(nN) * e(H * u^M, g^r)
        leftTerm1 = pairing.pairing(g1, y).powZn(Zr.newElement(n * N)).getImmutable(); // e(g_1, y)^(nN)
        leftTerm2 = pairing.pairing(id, gamma).powZn(Zr.newElement(n * N)).getImmutable(); // e(id, gamma)^(nN)
        leftTerm3 = pairing.pairing(H.mul(u.powZn(M)), g.powZn(r)).getImmutable(); // e(H * u^M, g^r)

        // 最终结果
        RResult = leftTerm1.mul(leftTerm2).mul(leftTerm3).getImmutable();
        // 验证双线性对等式
        if (LResult.isEqual(RResult)) {
            System.out.println("验证成功: 双线性对等式成立，接受上传数据。");
        } else {
            System.out.println("验证失败: 请HIC重新上传数据。");
        }
    }
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    @Override
    public void challenge() {
        System.out.println("-------------------TPA挑战阶段----------------------");
        // 获取文件分块的数量 n
        int n = fileParts.size();
        int I = n / 2;

        Set<Integer> selectedIndices = new HashSet<>(); // 使用 Set 来确保唯一性
        Random random = new Random();

        // 随机选择 I 个唯一的下标
        while (selectedIndices.size() < I) {
            int randomIndex = random.nextInt(n); // 生成范围为 0 到 n-1 的随机索引
            selectedIndices.add(randomIndex); // 将唯一的索引添加到集合中
        }

        // 将选择的下标转换为列表
        iList.addAll(selectedIndices);

        // 为每个选择的下标生成随机数 v_i
        for (int index : iList) {
            v_i = Zr.newRandomElement().getImmutable(); // 生成随机数 v_i
            vList.add(v_i); // 存储随机数 v_i
//            System.out.println("选择的下标: " + index + ", 生成的随机数 v_" + index + ": " + v_i);
        }
    }
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    @Override
    public void prove() {
        System.out.println("-------------------CLOUD返回证明阶段----------------------");
        // 计算 sigma = ∏ (sigma_i)^(v_i)
        sigma = G1.newOneElement(); // 初始化 sigma 为 1
        for (int k = 0; k < iList.size(); k++) {
            int index = iList.get(k); // 获取当前下标
            v_i = vList.get(k); // 获取对应的随机数 v_i
            sigma_i = sigma_iList.get(index); // 获取对应的 sigma_i
            // 计算 (sigma_i)^(v_i) 并累乘
            sigma = sigma.mul(sigma_i.powZn(v_i)).getImmutable();
        }
        System.out.println("计算得到的 sigma: " + sigma);

        // 计算 lambda_j = Σ (v_i × m_ij) mod q，i 为 iList 对应的值，j 从 1 到 N
        int N = 5; // 假设每个数据块有 N 个副本
        for (int j = 0; j < N; j++) {
            lambda_j = Zr.newZeroElement(); // 初始化 lambda_j 为 0

            for (int k = 0; k < iList.size(); k++) {
                int i = iList.get(k); // 获取当前 iList 中的下标
                m_ij = m_ijList.get(i * N + j); // 通过下标 i 和 j 获取 m_ij

                // 累加 v_i × m_ij
                Element v_i = vList.get(k); // 获取对应的随机数 v_i
                lambda_j = lambda_j.add(v_i.mul(m_ij)).getImmutable(); // lambda_j += v_i × m_ij
            }

            lambdaList.add(lambda_j); // 将计算得到的 lambda_j 添加到列表
            System.out.println("计算得到的 lambda_" + (j + 1) + ": " + lambda_j);
        }
    }
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    @Override
    public void verify() {
        System.out.println("-------------------验证阶段----------------------");
        int N = 5;

        // 计算 v_I = N × Σv_i
        v_I = Zr.newZeroElement(); // 初始化 v_I 为 0
        for (int i = 0; i < iList.size(); i++) {
            v_I = v_I.add(vList.get(i)).getImmutable(); // 累加 v_i
        }
        v_I = v_I.mul(Zr.newElement(N)).getImmutable(); // 计算 v_I = N × Σv_i

        // 计算 H_I = ∏(h_ij)^(v_i)，其中 i 是 iList 中的 i，j 从 1 到 N
        H_I = G1.newOneElement(); // 初始化 H_I 为 1
        for (int i : iList) {
            for (int j = 1; j <= N; j++) {
                Element h_ij = h_ijList.get(i * N + (j - 1)); // 根据 i 和 j 获取 h_{ij} 值
                Element v_i = vList.get(iList.indexOf(i)); // 获取对应的 v_i
                H_I = H_I.mul(h_ij.powZn(v_i)).getImmutable(); // 计算 H_I = H_I × (h_{ij})^(v_i)
            }
        }
        // 输出计算得到的 H_I
//        System.out.println("计算得到的 H_I: " + H_I);

        // 计算 Lambda = Σlambda_j，其中 j 从 1 到 N
        Lambda = Zr.newZeroElement(); // 初始化 Lambda 为 0
        for (Element lambda_j : lambdaList) {
            Lambda = Lambda.add(lambda_j).getImmutable(); // 累加 λ_j
        }

        // 使用双线性映射计算 e(sigma, g)
        e_sigma_g = pairing.pairing(sigma, g).getImmutable(); // 计算 e(sigma, g)
//        System.out.println("计算得到的 e(sigma, g): " + e_sigma_g);

        // 计算右侧表达式
        term1 = pairing.pairing(g1, y).powZn(v_I);              // e(g1, y)^v_I
        term2 = pairing.pairing(id, gamma).powZn(v_I);          // e(id, gamma)^v_I
        term3 = pairing.pairing(
                H_I.mul(u.powZn(Lambda)),  // H_I * u^Lambda
                g.powZn(r)                 // g^r
        ).getImmutable();

        Element rightSide = term1.mul(term2).mul(term3).getImmutable();

//        System.out.println("计算得到的右侧表达式: " + rightSide);

        // 判断等式是否相等
        if (e_sigma_g.equals(rightSide)) {
            System.out.println("验证通过：e(sigma, g) 等于右侧表达式。");
        } else {
            System.out.println("验证失败：e(sigma, g) 不等于右侧表达式。");
        }
    }
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    @Override
    public void HIC() {
        System.out.println("-------------------HIC计算H_II挑战阶段----------------------");
        int N = 5;
        // 计算 v_I = N × Σv_i
        v_II = Zr.newZeroElement(); // 初始化 v_I 为 0
        for (int i = 0; i < iList.size(); i++) {
            v_I = v_I.add(vList.get(i)).getImmutable(); // 累加 v_i
        }
        v_II = v_I.mul(Zr.newElement(N)).getImmutable(); // 计算 v_I = N × Σv_i

        // 计算 H_I = ∏(h_ij)^(v_i)，其中 i 是 iList 中的 i，j 从 1 到 N
        H_II = G1.newOneElement(); // 初始化 H_I 为 1
        for (int i : iList) {
            for (int j = 1; j <= N; j++) {
                Element h_ij = h_ijList.get(i * N + (j - 1)); // 根据 i 和 j 获取 h_{ij} 值
                Element v_i = vList.get(iList.indexOf(i)); // 获取对应的 v_i
                H_I = H_I.mul(h_ij.powZn(v_i)).getImmutable(); // 计算 H_I = H_I × (h_{ij})^(v_i)
            }
        }
    }
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    public static void main(String[] args) {
        BasicIdent2 ident = new BasicIdent2();
        // 动态代理，统计各个方法耗时
        Ident identProxy = (Ident) Proxy.newProxyInstance(
                BasicIdent2.class.getClassLoader(),
                new Class[] { Ident.class }, new TimeCountProxyHandle(ident));

        identProxy.buildSystem();
        identProxy.extractSecretKey();
        identProxy.authenticator();
        identProxy.challenge();
        identProxy.prove();
        identProxy.verify();
        identProxy.HIC();
    }

}