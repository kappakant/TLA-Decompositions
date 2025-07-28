---- MODULE paxos_epr_chunk2_IndQuickCheck ----
EXTENDS paxos_epr,Naturals,TLC

CONSTANT a1,a2,a3,v1,v2
VARIABLE Inv0_val
VARIABLE Inv1_val
VARIABLE Inv10_val
VARIABLE Inv100_val
VARIABLE Inv101_val
VARIABLE Inv102_val
VARIABLE Inv103_val
VARIABLE Inv104_val
VARIABLE Inv105_val
VARIABLE Inv106_val
VARIABLE Inv107_val
VARIABLE Inv108_val
VARIABLE Inv109_val
VARIABLE Inv11_val
VARIABLE Inv110_val
VARIABLE Inv111_val
VARIABLE Inv112_val
VARIABLE Inv113_val
VARIABLE Inv114_val
VARIABLE Inv115_val
VARIABLE Inv116_val
VARIABLE Inv117_val
VARIABLE Inv118_val
VARIABLE Inv119_val
VARIABLE Inv12_val
VARIABLE Inv120_val
VARIABLE Inv121_val
VARIABLE Inv122_val
VARIABLE Inv123_val
VARIABLE Inv124_val
VARIABLE Inv125_val
VARIABLE Inv126_val
VARIABLE Inv127_val
VARIABLE Inv128_val
VARIABLE Inv129_val
VARIABLE Inv13_val
VARIABLE Inv130_val
VARIABLE Inv131_val
VARIABLE Inv132_val
VARIABLE Inv133_val
VARIABLE Inv134_val
VARIABLE Inv135_val
VARIABLE Inv136_val
VARIABLE Inv137_val
VARIABLE Inv138_val
VARIABLE Inv139_val
VARIABLE Inv14_val
VARIABLE Inv140_val
VARIABLE Inv141_val
VARIABLE Inv142_val
VARIABLE Inv143_val
VARIABLE Inv144_val
VARIABLE Inv145_val
VARIABLE Inv146_val
VARIABLE Inv147_val
VARIABLE Inv148_val
VARIABLE Inv149_val
VARIABLE Inv15_val
VARIABLE Inv150_val
VARIABLE Inv151_val
VARIABLE Inv152_val
VARIABLE Inv153_val
VARIABLE Inv154_val
VARIABLE Inv155_val
VARIABLE Inv156_val
VARIABLE Inv157_val
VARIABLE Inv158_val
VARIABLE Inv159_val
VARIABLE Inv16_val
VARIABLE Inv160_val
VARIABLE Inv161_val
VARIABLE Inv162_val
VARIABLE Inv163_val
VARIABLE Inv164_val
VARIABLE Inv165_val
VARIABLE Inv166_val
VARIABLE Inv167_val
VARIABLE Inv168_val
VARIABLE Inv169_val
VARIABLE Inv17_val
VARIABLE Inv170_val
VARIABLE Inv171_val
VARIABLE Inv172_val
VARIABLE Inv173_val
VARIABLE Inv174_val
VARIABLE Inv175_val
VARIABLE Inv176_val
VARIABLE Inv177_val
VARIABLE Inv178_val
VARIABLE Inv179_val
VARIABLE Inv18_val
VARIABLE Inv180_val
VARIABLE Inv181_val
VARIABLE Inv182_val
VARIABLE Inv183_val
VARIABLE Inv184_val
VARIABLE Inv185_val
VARIABLE Inv186_val
VARIABLE Inv187_val
VARIABLE Inv188_val
VARIABLE Inv189_val
VARIABLE Inv19_val
VARIABLE Inv190_val
VARIABLE Inv191_val
VARIABLE Inv192_val
VARIABLE Inv193_val
VARIABLE Inv194_val
VARIABLE Inv195_val
VARIABLE Inv196_val
VARIABLE Inv197_val
VARIABLE Inv198_val
VARIABLE Inv199_val
VARIABLE Inv2_val
VARIABLE Inv20_val
VARIABLE Inv200_val
VARIABLE Inv201_val
VARIABLE Inv202_val
VARIABLE Inv203_val
VARIABLE Inv204_val
VARIABLE Inv205_val
VARIABLE Inv206_val
VARIABLE Inv207_val
VARIABLE Inv208_val
VARIABLE Inv209_val
VARIABLE Inv21_val
VARIABLE Inv210_val
VARIABLE Inv211_val
VARIABLE Inv212_val
VARIABLE Inv213_val
VARIABLE Inv214_val
VARIABLE Inv215_val
VARIABLE Inv216_val
VARIABLE Inv217_val
VARIABLE Inv218_val
VARIABLE Inv219_val
VARIABLE Inv22_val
VARIABLE Inv220_val
VARIABLE Inv221_val
VARIABLE Inv222_val
VARIABLE Inv223_val
VARIABLE Inv224_val
VARIABLE Inv225_val
VARIABLE Inv226_val
VARIABLE Inv227_val
VARIABLE Inv228_val
VARIABLE Inv229_val
VARIABLE Inv23_val
VARIABLE Inv230_val
VARIABLE Inv231_val
VARIABLE Inv232_val
VARIABLE Inv233_val
VARIABLE Inv234_val
VARIABLE Inv235_val
VARIABLE Inv236_val
VARIABLE Inv237_val
VARIABLE Inv238_val
VARIABLE Inv239_val
VARIABLE Inv24_val
VARIABLE Inv240_val
VARIABLE Inv241_val
VARIABLE Inv242_val
VARIABLE Inv243_val
VARIABLE Inv244_val
VARIABLE Inv245_val
VARIABLE Inv246_val
VARIABLE Inv247_val
VARIABLE Inv248_val
VARIABLE Inv249_val
VARIABLE Inv25_val
VARIABLE Inv250_val
VARIABLE Inv251_val
VARIABLE Inv252_val
VARIABLE Inv253_val
VARIABLE Inv254_val
VARIABLE Inv255_val
VARIABLE Inv256_val
VARIABLE Inv257_val
VARIABLE Inv258_val
VARIABLE Inv259_val
VARIABLE Inv26_val
VARIABLE Inv260_val
VARIABLE Inv261_val
VARIABLE Inv262_val
VARIABLE Inv263_val
VARIABLE Inv264_val
VARIABLE Inv265_val
VARIABLE Inv266_val
VARIABLE Inv267_val
VARIABLE Inv268_val
VARIABLE Inv269_val
VARIABLE Inv27_val
VARIABLE Inv270_val
VARIABLE Inv271_val
VARIABLE Inv272_val
VARIABLE Inv273_val
VARIABLE Inv274_val
VARIABLE Inv275_val
VARIABLE Inv276_val
VARIABLE Inv277_val
VARIABLE Inv278_val
VARIABLE Inv279_val
VARIABLE Inv28_val
VARIABLE Inv280_val
VARIABLE Inv281_val
VARIABLE Inv282_val
VARIABLE Inv283_val
VARIABLE Inv284_val
VARIABLE Inv285_val
VARIABLE Inv286_val
VARIABLE Inv287_val
VARIABLE Inv288_val
VARIABLE Inv289_val
VARIABLE Inv29_val
VARIABLE Inv290_val
VARIABLE Inv291_val
VARIABLE Inv292_val
VARIABLE Inv293_val
VARIABLE Inv294_val
VARIABLE Inv295_val
VARIABLE Inv296_val
VARIABLE Inv297_val
VARIABLE Inv298_val
VARIABLE Inv299_val
VARIABLE Inv3_val
VARIABLE Inv30_val
VARIABLE Inv300_val
VARIABLE Inv301_val
VARIABLE Inv302_val
VARIABLE Inv303_val
VARIABLE Inv304_val
VARIABLE Inv305_val
VARIABLE Inv306_val
VARIABLE Inv307_val
VARIABLE Inv308_val
VARIABLE Inv309_val
VARIABLE Inv31_val
VARIABLE Inv310_val
VARIABLE Inv311_val
VARIABLE Inv312_val
VARIABLE Inv313_val
VARIABLE Inv314_val
VARIABLE Inv315_val
VARIABLE Inv316_val
VARIABLE Inv317_val
VARIABLE Inv318_val
VARIABLE Inv319_val
VARIABLE Inv32_val
VARIABLE Inv320_val
VARIABLE Inv321_val
VARIABLE Inv322_val
VARIABLE Inv323_val
VARIABLE Inv324_val
VARIABLE Inv325_val
VARIABLE Inv326_val
VARIABLE Inv327_val
VARIABLE Inv328_val
VARIABLE Inv329_val
VARIABLE Inv33_val
VARIABLE Inv330_val
VARIABLE Inv331_val
VARIABLE Inv332_val
VARIABLE Inv333_val
VARIABLE Inv334_val
VARIABLE Inv335_val
VARIABLE Inv336_val
VARIABLE Inv337_val
VARIABLE Inv338_val
VARIABLE Inv339_val
VARIABLE Inv34_val
VARIABLE Inv340_val
VARIABLE Inv341_val
VARIABLE Inv342_val
VARIABLE Inv343_val
VARIABLE Inv344_val
VARIABLE Inv345_val
VARIABLE Inv346_val
VARIABLE Inv347_val
VARIABLE Inv348_val
VARIABLE Inv349_val
VARIABLE Inv35_val
VARIABLE Inv350_val
VARIABLE Inv351_val
VARIABLE Inv352_val
VARIABLE Inv353_val
VARIABLE Inv354_val
VARIABLE Inv355_val
VARIABLE Inv356_val
VARIABLE Inv357_val
VARIABLE Inv358_val
VARIABLE Inv359_val
VARIABLE Inv36_val
VARIABLE Inv360_val
VARIABLE Inv361_val
VARIABLE Inv362_val
VARIABLE Inv363_val
VARIABLE Inv364_val
VARIABLE Inv365_val
VARIABLE Inv366_val
VARIABLE Inv367_val
VARIABLE Inv368_val
VARIABLE Inv369_val
VARIABLE Inv37_val
VARIABLE Inv370_val
VARIABLE Inv371_val
VARIABLE Inv372_val
VARIABLE Inv373_val
VARIABLE Inv374_val
VARIABLE Inv375_val
VARIABLE Inv376_val
VARIABLE Inv377_val
VARIABLE Inv378_val
VARIABLE Inv379_val
VARIABLE Inv38_val
VARIABLE Inv380_val
VARIABLE Inv381_val
VARIABLE Inv382_val
VARIABLE Inv383_val
VARIABLE Inv384_val
VARIABLE Inv385_val
VARIABLE Inv386_val
VARIABLE Inv387_val
VARIABLE Inv388_val
VARIABLE Inv389_val
VARIABLE Inv39_val
VARIABLE Inv390_val
VARIABLE Inv391_val
VARIABLE Inv392_val
VARIABLE Inv393_val
VARIABLE Inv394_val
VARIABLE Inv395_val
VARIABLE Inv396_val
VARIABLE Inv397_val
VARIABLE Inv398_val
VARIABLE Inv399_val
VARIABLE Inv4_val
VARIABLE Inv40_val
VARIABLE Inv400_val
VARIABLE Inv401_val
VARIABLE Inv402_val
VARIABLE Inv403_val
VARIABLE Inv404_val
VARIABLE Inv405_val
VARIABLE Inv406_val
VARIABLE Inv407_val
VARIABLE Inv408_val
VARIABLE Inv409_val
VARIABLE Inv41_val
VARIABLE Inv410_val
VARIABLE Inv411_val
VARIABLE Inv412_val
VARIABLE Inv413_val
VARIABLE Inv414_val
VARIABLE Inv415_val
VARIABLE Inv416_val
VARIABLE Inv417_val
VARIABLE Inv418_val
VARIABLE Inv419_val
VARIABLE Inv42_val
VARIABLE Inv420_val
VARIABLE Inv421_val
VARIABLE Inv422_val
VARIABLE Inv423_val
VARIABLE Inv424_val
VARIABLE Inv425_val
VARIABLE Inv426_val
VARIABLE Inv427_val
VARIABLE Inv428_val
VARIABLE Inv429_val
VARIABLE Inv43_val
VARIABLE Inv430_val
VARIABLE Inv431_val
VARIABLE Inv432_val
VARIABLE Inv433_val
VARIABLE Inv434_val
VARIABLE Inv435_val
VARIABLE Inv436_val
VARIABLE Inv437_val
VARIABLE Inv438_val
VARIABLE Inv439_val
VARIABLE Inv44_val
VARIABLE Inv440_val
VARIABLE Inv441_val
VARIABLE Inv442_val
VARIABLE Inv443_val
VARIABLE Inv444_val
VARIABLE Inv445_val
VARIABLE Inv446_val
VARIABLE Inv447_val
VARIABLE Inv448_val
VARIABLE Inv449_val
VARIABLE Inv45_val
VARIABLE Inv450_val
VARIABLE Inv451_val
VARIABLE Inv452_val
VARIABLE Inv453_val
VARIABLE Inv454_val
VARIABLE Inv455_val
VARIABLE Inv456_val
VARIABLE Inv457_val
VARIABLE Inv458_val
VARIABLE Inv459_val
VARIABLE Inv46_val
VARIABLE Inv460_val
VARIABLE Inv461_val
VARIABLE Inv462_val
VARIABLE Inv463_val
VARIABLE Inv464_val
VARIABLE Inv465_val
VARIABLE Inv466_val
VARIABLE Inv467_val
VARIABLE Inv468_val
VARIABLE Inv469_val
VARIABLE Inv47_val
VARIABLE Inv470_val
VARIABLE Inv471_val
VARIABLE Inv472_val
VARIABLE Inv473_val
VARIABLE Inv474_val
VARIABLE Inv475_val
VARIABLE Inv476_val
VARIABLE Inv477_val
VARIABLE Inv478_val
VARIABLE Inv479_val
VARIABLE Inv48_val
VARIABLE Inv480_val
VARIABLE Inv481_val
VARIABLE Inv482_val
VARIABLE Inv483_val
VARIABLE Inv484_val
VARIABLE Inv485_val
VARIABLE Inv486_val
VARIABLE Inv487_val
VARIABLE Inv488_val
VARIABLE Inv489_val
VARIABLE Inv49_val
VARIABLE Inv490_val
VARIABLE Inv491_val
VARIABLE Inv492_val
VARIABLE Inv493_val
VARIABLE Inv494_val
VARIABLE Inv495_val
VARIABLE Inv496_val
VARIABLE Inv497_val
VARIABLE Inv498_val
VARIABLE Inv499_val
VARIABLE Inv5_val
VARIABLE Inv50_val
VARIABLE Inv500_val
VARIABLE Inv501_val
VARIABLE Inv502_val
VARIABLE Inv503_val
VARIABLE Inv504_val
VARIABLE Inv505_val
VARIABLE Inv506_val
VARIABLE Inv507_val
VARIABLE Inv508_val
VARIABLE Inv509_val
VARIABLE Inv51_val
VARIABLE Inv510_val
VARIABLE Inv511_val
VARIABLE Inv512_val
VARIABLE Inv513_val
VARIABLE Inv514_val
VARIABLE Inv515_val
VARIABLE Inv516_val
VARIABLE Inv517_val
VARIABLE Inv518_val
VARIABLE Inv519_val
VARIABLE Inv52_val
VARIABLE Inv520_val
VARIABLE Inv521_val
VARIABLE Inv522_val
VARIABLE Inv523_val
VARIABLE Inv524_val
VARIABLE Inv525_val
VARIABLE Inv526_val
VARIABLE Inv527_val
VARIABLE Inv528_val
VARIABLE Inv529_val
VARIABLE Inv53_val
VARIABLE Inv530_val
VARIABLE Inv531_val
VARIABLE Inv532_val
VARIABLE Inv533_val
VARIABLE Inv534_val
VARIABLE Inv535_val
VARIABLE Inv536_val
VARIABLE Inv537_val
VARIABLE Inv538_val
VARIABLE Inv539_val
VARIABLE Inv54_val
VARIABLE Inv540_val
VARIABLE Inv541_val
VARIABLE Inv542_val
VARIABLE Inv543_val
VARIABLE Inv544_val
VARIABLE Inv545_val
VARIABLE Inv546_val
VARIABLE Inv547_val
VARIABLE Inv548_val
VARIABLE Inv549_val
VARIABLE Inv55_val
VARIABLE Inv550_val
VARIABLE Inv551_val
VARIABLE Inv552_val
VARIABLE Inv553_val
VARIABLE Inv554_val
VARIABLE Inv555_val
VARIABLE Inv556_val
VARIABLE Inv557_val
VARIABLE Inv558_val
VARIABLE Inv559_val
VARIABLE Inv56_val
VARIABLE Inv560_val
VARIABLE Inv561_val
VARIABLE Inv562_val
VARIABLE Inv563_val
VARIABLE Inv564_val
VARIABLE Inv565_val
VARIABLE Inv566_val
VARIABLE Inv567_val
VARIABLE Inv568_val
VARIABLE Inv569_val
VARIABLE Inv57_val
VARIABLE Inv570_val
VARIABLE Inv571_val
VARIABLE Inv572_val
VARIABLE Inv573_val
VARIABLE Inv574_val
VARIABLE Inv575_val
VARIABLE Inv576_val
VARIABLE Inv577_val
VARIABLE Inv578_val
VARIABLE Inv579_val
VARIABLE Inv58_val
VARIABLE Inv580_val
VARIABLE Inv581_val
VARIABLE Inv582_val
VARIABLE Inv583_val
VARIABLE Inv584_val
VARIABLE Inv585_val
VARIABLE Inv586_val
VARIABLE Inv587_val
VARIABLE Inv588_val
VARIABLE Inv589_val
VARIABLE Inv59_val
VARIABLE Inv590_val
VARIABLE Inv591_val
VARIABLE Inv592_val
VARIABLE Inv593_val
VARIABLE Inv594_val
VARIABLE Inv595_val
VARIABLE Inv596_val
VARIABLE Inv597_val
VARIABLE Inv598_val
VARIABLE Inv599_val
VARIABLE Inv6_val
VARIABLE Inv60_val
VARIABLE Inv600_val
VARIABLE Inv601_val
VARIABLE Inv602_val
VARIABLE Inv603_val
VARIABLE Inv604_val
VARIABLE Inv605_val
VARIABLE Inv606_val
VARIABLE Inv607_val
VARIABLE Inv608_val
VARIABLE Inv609_val
VARIABLE Inv61_val
VARIABLE Inv610_val
VARIABLE Inv611_val
VARIABLE Inv612_val
VARIABLE Inv613_val
VARIABLE Inv614_val
VARIABLE Inv615_val
VARIABLE Inv616_val
VARIABLE Inv617_val
VARIABLE Inv618_val
VARIABLE Inv619_val
VARIABLE Inv62_val
VARIABLE Inv620_val
VARIABLE Inv621_val
VARIABLE Inv622_val
VARIABLE Inv623_val
VARIABLE Inv624_val
VARIABLE Inv625_val
VARIABLE Inv626_val
VARIABLE Inv627_val
VARIABLE Inv628_val
VARIABLE Inv629_val
VARIABLE Inv63_val
VARIABLE Inv630_val
VARIABLE Inv631_val
VARIABLE Inv632_val
VARIABLE Inv633_val
VARIABLE Inv634_val
VARIABLE Inv635_val
VARIABLE Inv636_val
VARIABLE Inv637_val
VARIABLE Inv638_val
VARIABLE Inv639_val
VARIABLE Inv64_val
VARIABLE Inv640_val
VARIABLE Inv641_val
VARIABLE Inv642_val
VARIABLE Inv643_val
VARIABLE Inv644_val
VARIABLE Inv645_val
VARIABLE Inv646_val
VARIABLE Inv647_val
VARIABLE Inv648_val
VARIABLE Inv649_val
VARIABLE Inv65_val
VARIABLE Inv650_val
VARIABLE Inv651_val
VARIABLE Inv652_val
VARIABLE Inv653_val
VARIABLE Inv654_val
VARIABLE Inv655_val
VARIABLE Inv656_val
VARIABLE Inv657_val
VARIABLE Inv658_val
VARIABLE Inv659_val
VARIABLE Inv66_val
VARIABLE Inv660_val
VARIABLE Inv661_val
VARIABLE Inv662_val
VARIABLE Inv663_val
VARIABLE Inv664_val
VARIABLE Inv665_val
VARIABLE Inv666_val
VARIABLE Inv667_val
VARIABLE Inv668_val
VARIABLE Inv669_val
VARIABLE Inv67_val
VARIABLE Inv670_val
VARIABLE Inv671_val
VARIABLE Inv672_val
VARIABLE Inv673_val
VARIABLE Inv674_val
VARIABLE Inv675_val
VARIABLE Inv676_val
VARIABLE Inv677_val
VARIABLE Inv678_val
VARIABLE Inv679_val
VARIABLE Inv68_val
VARIABLE Inv680_val
VARIABLE Inv681_val
VARIABLE Inv682_val
VARIABLE Inv683_val
VARIABLE Inv684_val
VARIABLE Inv685_val
VARIABLE Inv686_val
VARIABLE Inv687_val
VARIABLE Inv688_val
VARIABLE Inv689_val
VARIABLE Inv69_val
VARIABLE Inv690_val
VARIABLE Inv691_val
VARIABLE Inv692_val
VARIABLE Inv693_val
VARIABLE Inv694_val
VARIABLE Inv695_val
VARIABLE Inv696_val
VARIABLE Inv697_val
VARIABLE Inv698_val
VARIABLE Inv699_val
VARIABLE Inv7_val
VARIABLE Inv70_val
VARIABLE Inv700_val
VARIABLE Inv701_val
VARIABLE Inv702_val
VARIABLE Inv703_val
VARIABLE Inv704_val
VARIABLE Inv705_val
VARIABLE Inv706_val
VARIABLE Inv707_val
VARIABLE Inv708_val
VARIABLE Inv709_val
VARIABLE Inv71_val
VARIABLE Inv710_val
VARIABLE Inv711_val
VARIABLE Inv712_val
VARIABLE Inv713_val
VARIABLE Inv714_val
VARIABLE Inv715_val
VARIABLE Inv716_val
VARIABLE Inv717_val
VARIABLE Inv718_val
VARIABLE Inv719_val
VARIABLE Inv72_val
VARIABLE Inv720_val
VARIABLE Inv721_val
VARIABLE Inv722_val
VARIABLE Inv723_val
VARIABLE Inv724_val
VARIABLE Inv725_val
VARIABLE Inv726_val
VARIABLE Inv727_val
VARIABLE Inv728_val
VARIABLE Inv729_val
VARIABLE Inv73_val
VARIABLE Inv730_val
VARIABLE Inv731_val
VARIABLE Inv732_val
VARIABLE Inv733_val
VARIABLE Inv734_val
VARIABLE Inv735_val
VARIABLE Inv736_val
VARIABLE Inv737_val
VARIABLE Inv738_val
VARIABLE Inv739_val
VARIABLE Inv74_val
VARIABLE Inv740_val
VARIABLE Inv741_val
VARIABLE Inv742_val
VARIABLE Inv743_val
VARIABLE Inv744_val
VARIABLE Inv745_val
VARIABLE Inv746_val
VARIABLE Inv747_val
VARIABLE Inv748_val
VARIABLE Inv749_val
VARIABLE Inv75_val
VARIABLE Inv750_val
VARIABLE Inv751_val
VARIABLE Inv752_val
VARIABLE Inv753_val
VARIABLE Inv754_val
VARIABLE Inv755_val
VARIABLE Inv756_val
VARIABLE Inv757_val
VARIABLE Inv758_val
VARIABLE Inv759_val
VARIABLE Inv76_val
VARIABLE Inv77_val
VARIABLE Inv78_val
VARIABLE Inv79_val
VARIABLE Inv8_val
VARIABLE Inv80_val
VARIABLE Inv81_val
VARIABLE Inv82_val
VARIABLE Inv83_val
VARIABLE Inv84_val
VARIABLE Inv85_val
VARIABLE Inv86_val
VARIABLE Inv87_val
VARIABLE Inv88_val
VARIABLE Inv89_val
VARIABLE Inv9_val
VARIABLE Inv90_val
VARIABLE Inv91_val
VARIABLE Inv92_val
VARIABLE Inv93_val
VARIABLE Inv94_val
VARIABLE Inv95_val
VARIABLE Inv96_val
VARIABLE Inv97_val
VARIABLE Inv98_val
VARIABLE Inv99_val
VARIABLE ctiId

Inv0 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ (((r > m)))
Inv1 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ ((<<m, val>> \in proposal))
Inv10 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ ((m <= r))
Inv100 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ (~(<<r, val>> \in proposal))
Inv101 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv102 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ (~(m <= r))
Inv103 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ (~(m \in one_a))
Inv104 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ (~(n \in q))
Inv105 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ (~(one_a = one_a \cup {r}))
Inv106 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv107 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ (~(r <= m))
Inv108 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ (~(r = None))
Inv109 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ (~(r \in one_a))
Inv11 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ ((m \in one_a))
Inv110 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv111 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ ((<<n, m>> \in left_rnd))
Inv112 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ ((<<n, m>> \in one_b))
Inv113 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ ((<<n, r, val>> \in vote))
Inv114 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ ((<<n, r>> \in left_rnd))
Inv115 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ ((<<n, r>> \in one_b))
Inv116 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ ((<<r, val>> \in proposal))
Inv117 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ ((decision = decision \cup {<<n, r, val>>}))
Inv118 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ ((m <= r))
Inv119 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ ((m \in one_a))
Inv12 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ ((n \in q))
Inv120 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ ((n \in q))
Inv121 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ ((one_a = one_a \cup {r}))
Inv122 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ ((proposal = proposal \cup {<<r, val>>}))
Inv123 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ ((r <= m))
Inv124 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ ((r = None))
Inv125 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ ((r \in one_a))
Inv126 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ ((vote = vote \cup {<<n, r, val>>}))
Inv127 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ (~((m > r)))
Inv128 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ (~((r > m)))
Inv129 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ (~(<<m, val>> \in proposal))
Inv13 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ ((one_a = one_a \cup {r}))
Inv130 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ (~(<<n, m>> \in left_rnd))
Inv131 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ (~(<<n, m>> \in one_b))
Inv132 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ (~(<<n, r, val>> \in vote))
Inv133 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ (~(<<n, r>> \in left_rnd))
Inv134 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ (~(<<n, r>> \in one_b))
Inv135 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ (~(<<r, val>> \in proposal))
Inv136 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv137 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ (~(m <= r))
Inv138 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ (~(m \in one_a))
Inv139 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ (~(n \in q))
Inv14 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ ((proposal = proposal \cup {<<r, val>>}))
Inv140 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ (~(one_a = one_a \cup {r}))
Inv141 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv142 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ (~(r <= m))
Inv143 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ (~(r = None))
Inv144 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ (~(r \in one_a))
Inv145 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m, val>> \in vote) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv146 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ ((<<n, m>> \in one_b))
Inv147 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ ((<<n, r, val>> \in vote))
Inv148 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ ((<<n, r>> \in left_rnd))
Inv149 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ ((<<n, r>> \in one_b))
Inv15 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ ((r <= m))
Inv150 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ ((<<r, val>> \in proposal))
Inv151 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ ((decision = decision \cup {<<n, r, val>>}))
Inv152 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ ((m <= r))
Inv153 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ ((m \in one_a))
Inv154 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ ((n \in q))
Inv155 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ ((one_a = one_a \cup {r}))
Inv156 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ ((proposal = proposal \cup {<<r, val>>}))
Inv157 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ ((r <= m))
Inv158 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ ((r = None))
Inv159 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ ((r \in one_a))
Inv16 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ ((r = None))
Inv160 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ ((vote = vote \cup {<<n, r, val>>}))
Inv161 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ (~((m > r)))
Inv162 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ (~((r > m)))
Inv163 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ (~(<<m, val>> \in proposal))
Inv164 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ (~(<<n, m, val>> \in vote))
Inv165 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ (~(<<n, m>> \in one_b))
Inv166 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ (~(<<n, r, val>> \in vote))
Inv167 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ (~(<<n, r>> \in left_rnd))
Inv168 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ (~(<<n, r>> \in one_b))
Inv169 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ (~(<<r, val>> \in proposal))
Inv17 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ ((r \in one_a))
Inv170 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv171 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ (~(m <= r))
Inv172 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ (~(m \in one_a))
Inv173 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ (~(n \in q))
Inv174 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ (~(one_a = one_a \cup {r}))
Inv175 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv176 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ (~(r <= m))
Inv177 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ (~(r = None))
Inv178 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ (~(r \in one_a))
Inv179 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in left_rnd) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv18 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ ((vote = vote \cup {<<n, r, val>>}))
Inv180 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ ((<<n, r, val>> \in vote))
Inv181 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ ((<<n, r>> \in left_rnd))
Inv182 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ ((<<n, r>> \in one_b))
Inv183 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ ((<<r, val>> \in proposal))
Inv184 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ ((decision = decision \cup {<<n, r, val>>}))
Inv185 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ ((m <= r))
Inv186 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ ((m \in one_a))
Inv187 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ ((n \in q))
Inv188 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ ((one_a = one_a \cup {r}))
Inv189 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ ((proposal = proposal \cup {<<r, val>>}))
Inv19 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ (~((r > m)))
Inv190 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ ((r <= m))
Inv191 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ ((r = None))
Inv192 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ ((r \in one_a))
Inv193 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ ((vote = vote \cup {<<n, r, val>>}))
Inv194 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ (~((m > r)))
Inv195 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ (~((r > m)))
Inv196 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ (~(<<m, val>> \in proposal))
Inv197 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ (~(<<n, m, val>> \in vote))
Inv198 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ (~(<<n, m>> \in left_rnd))
Inv199 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ (~(<<n, r, val>> \in vote))
Inv2 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ ((<<n, m, val>> \in vote))
Inv20 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ (~(<<m, val>> \in proposal))
Inv200 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ (~(<<n, r>> \in left_rnd))
Inv201 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ (~(<<n, r>> \in one_b))
Inv202 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ (~(<<r, val>> \in proposal))
Inv203 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv204 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ (~(m <= r))
Inv205 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ (~(m \in one_a))
Inv206 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ (~(n \in q))
Inv207 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ (~(one_a = one_a \cup {r}))
Inv208 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv209 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ (~(r <= m))
Inv21 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ (~(<<n, m, val>> \in vote))
Inv210 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ (~(r = None))
Inv211 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ (~(r \in one_a))
Inv212 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, m>> \in one_b) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv213 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ ((<<n, r>> \in left_rnd))
Inv214 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ ((<<n, r>> \in one_b))
Inv215 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ ((<<r, val>> \in proposal))
Inv216 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ ((decision = decision \cup {<<n, r, val>>}))
Inv217 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ ((m <= r))
Inv218 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ ((m \in one_a))
Inv219 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ ((n \in q))
Inv22 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ (~(<<n, m>> \in left_rnd))
Inv220 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ ((one_a = one_a \cup {r}))
Inv221 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ ((proposal = proposal \cup {<<r, val>>}))
Inv222 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ ((r <= m))
Inv223 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ ((r = None))
Inv224 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ ((r \in one_a))
Inv225 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ ((vote = vote \cup {<<n, r, val>>}))
Inv226 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ (~((m > r)))
Inv227 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ (~((r > m)))
Inv228 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ (~(<<m, val>> \in proposal))
Inv229 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ (~(<<n, m, val>> \in vote))
Inv23 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ (~(<<n, m>> \in one_b))
Inv230 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ (~(<<n, m>> \in left_rnd))
Inv231 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ (~(<<n, m>> \in one_b))
Inv232 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ (~(<<n, r>> \in left_rnd))
Inv233 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ (~(<<n, r>> \in one_b))
Inv234 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ (~(<<r, val>> \in proposal))
Inv235 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv236 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ (~(m <= r))
Inv237 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ (~(m \in one_a))
Inv238 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ (~(n \in q))
Inv239 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ (~(one_a = one_a \cup {r}))
Inv24 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ (~(<<n, r, val>> \in vote))
Inv240 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv241 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ (~(r <= m))
Inv242 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ (~(r = None))
Inv243 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ (~(r \in one_a))
Inv244 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r, val>> \in vote) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv245 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ ((<<n, r>> \in one_b))
Inv246 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ ((<<r, val>> \in proposal))
Inv247 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ ((decision = decision \cup {<<n, r, val>>}))
Inv248 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ ((m <= r))
Inv249 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ ((m \in one_a))
Inv25 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ (~(<<n, r>> \in left_rnd))
Inv250 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ ((n \in q))
Inv251 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ ((one_a = one_a \cup {r}))
Inv252 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ ((proposal = proposal \cup {<<r, val>>}))
Inv253 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ ((r <= m))
Inv254 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ ((r = None))
Inv255 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ ((r \in one_a))
Inv256 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ ((vote = vote \cup {<<n, r, val>>}))
Inv257 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ (~((m > r)))
Inv258 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ (~((r > m)))
Inv259 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ (~(<<m, val>> \in proposal))
Inv26 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ (~(<<n, r>> \in one_b))
Inv260 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ (~(<<n, m, val>> \in vote))
Inv261 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ (~(<<n, m>> \in left_rnd))
Inv262 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ (~(<<n, m>> \in one_b))
Inv263 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ (~(<<n, r, val>> \in vote))
Inv264 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ (~(<<n, r>> \in one_b))
Inv265 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ (~(<<r, val>> \in proposal))
Inv266 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv267 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ (~(m <= r))
Inv268 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ (~(m \in one_a))
Inv269 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ (~(n \in q))
Inv27 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ (~(<<r, val>> \in proposal))
Inv270 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ (~(one_a = one_a \cup {r}))
Inv271 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv272 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ (~(r <= m))
Inv273 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ (~(r = None))
Inv274 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ (~(r \in one_a))
Inv275 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in left_rnd) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv276 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ ((<<r, val>> \in proposal))
Inv277 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ ((decision = decision \cup {<<n, r, val>>}))
Inv278 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ ((m <= r))
Inv279 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ ((m \in one_a))
Inv28 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv280 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ ((n \in q))
Inv281 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ ((one_a = one_a \cup {r}))
Inv282 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ ((proposal = proposal \cup {<<r, val>>}))
Inv283 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ ((r <= m))
Inv284 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ ((r = None))
Inv285 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ ((r \in one_a))
Inv286 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ ((vote = vote \cup {<<n, r, val>>}))
Inv287 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ (~((m > r)))
Inv288 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ (~((r > m)))
Inv289 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ (~(<<m, val>> \in proposal))
Inv29 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ (~(m <= r))
Inv290 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ (~(<<n, m, val>> \in vote))
Inv291 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ (~(<<n, m>> \in left_rnd))
Inv292 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ (~(<<n, m>> \in one_b))
Inv293 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ (~(<<n, r, val>> \in vote))
Inv294 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ (~(<<n, r>> \in left_rnd))
Inv295 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ (~(<<r, val>> \in proposal))
Inv296 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv297 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ (~(m <= r))
Inv298 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ (~(m \in one_a))
Inv299 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ (~(n \in q))
Inv3 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ ((<<n, m>> \in left_rnd))
Inv30 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ (~(m \in one_a))
Inv300 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ (~(one_a = one_a \cup {r}))
Inv301 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv302 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ (~(r <= m))
Inv303 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ (~(r = None))
Inv304 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ (~(r \in one_a))
Inv305 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<n, r>> \in one_b) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv306 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ ((decision = decision \cup {<<n, r, val>>}))
Inv307 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ ((m <= r))
Inv308 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ ((m \in one_a))
Inv309 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ ((n \in q))
Inv31 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ (~(n \in q))
Inv310 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ ((one_a = one_a \cup {r}))
Inv311 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ ((proposal = proposal \cup {<<r, val>>}))
Inv312 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ ((r <= m))
Inv313 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ ((r = None))
Inv314 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ ((r \in one_a))
Inv315 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ ((vote = vote \cup {<<n, r, val>>}))
Inv316 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ (~((m > r)))
Inv317 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ (~((r > m)))
Inv318 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ (~(<<m, val>> \in proposal))
Inv319 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ (~(<<n, m, val>> \in vote))
Inv32 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ (~(one_a = one_a \cup {r}))
Inv320 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ (~(<<n, m>> \in left_rnd))
Inv321 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ (~(<<n, m>> \in one_b))
Inv322 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ (~(<<n, r, val>> \in vote))
Inv323 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ (~(<<n, r>> \in left_rnd))
Inv324 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ (~(<<n, r>> \in one_b))
Inv325 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv326 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ (~(m <= r))
Inv327 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ (~(m \in one_a))
Inv328 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ (~(n \in q))
Inv329 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ (~(one_a = one_a \cup {r}))
Inv33 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv330 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv331 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ (~(r <= m))
Inv332 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ (~(r = None))
Inv333 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ (~(r \in one_a))
Inv334 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<r, val>> \in proposal) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv335 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ ((m <= r))
Inv336 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ ((m \in one_a))
Inv337 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ ((n \in q))
Inv338 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ ((one_a = one_a \cup {r}))
Inv339 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ ((proposal = proposal \cup {<<r, val>>}))
Inv34 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ (~(r <= m))
Inv340 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ ((r <= m))
Inv341 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ ((r = None))
Inv342 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ ((r \in one_a))
Inv343 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ ((vote = vote \cup {<<n, r, val>>}))
Inv344 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ (~((m > r)))
Inv345 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ (~((r > m)))
Inv346 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ (~(<<m, val>> \in proposal))
Inv347 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ (~(<<n, m, val>> \in vote))
Inv348 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ (~(<<n, m>> \in left_rnd))
Inv349 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ (~(<<n, m>> \in one_b))
Inv35 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ (~(r = None))
Inv350 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ (~(<<n, r, val>> \in vote))
Inv351 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ (~(<<n, r>> \in left_rnd))
Inv352 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ (~(<<n, r>> \in one_b))
Inv353 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ (~(<<r, val>> \in proposal))
Inv354 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ (~(m <= r))
Inv355 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ (~(m \in one_a))
Inv356 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ (~(n \in q))
Inv357 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ (~(one_a = one_a \cup {r}))
Inv358 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv359 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ (~(r <= m))
Inv36 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ (~(r \in one_a))
Inv360 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ (~(r = None))
Inv361 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ (~(r \in one_a))
Inv362 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (decision = decision \cup {<<n, r, val>>}) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv363 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m <= r) \/ ((m \in one_a))
Inv364 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m <= r) \/ ((n \in q))
Inv365 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m <= r) \/ ((one_a = one_a \cup {r}))
Inv366 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m <= r) \/ ((proposal = proposal \cup {<<r, val>>}))
Inv367 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m <= r) \/ ((r <= m))
Inv368 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m <= r) \/ ((r = None))
Inv369 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m <= r) \/ ((r \in one_a))
Inv37 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv370 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m <= r) \/ ((vote = vote \cup {<<n, r, val>>}))
Inv371 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m <= r) \/ (~((m > r)))
Inv372 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m <= r) \/ (~((r > m)))
Inv373 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m <= r) \/ (~(<<m, val>> \in proposal))
Inv374 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m <= r) \/ (~(<<n, m, val>> \in vote))
Inv375 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m <= r) \/ (~(<<n, m>> \in left_rnd))
Inv376 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m <= r) \/ (~(<<n, m>> \in one_b))
Inv377 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m <= r) \/ (~(<<n, r, val>> \in vote))
Inv378 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m <= r) \/ (~(<<n, r>> \in left_rnd))
Inv379 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m <= r) \/ (~(<<n, r>> \in one_b))
Inv38 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ ((<<m, val>> \in proposal))
Inv380 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m <= r) \/ (~(<<r, val>> \in proposal))
Inv381 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m <= r) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv382 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m <= r) \/ (~(m \in one_a))
Inv383 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m <= r) \/ (~(n \in q))
Inv384 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m <= r) \/ (~(one_a = one_a \cup {r}))
Inv385 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m <= r) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv386 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m <= r) \/ (~(r <= m))
Inv387 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m <= r) \/ (~(r = None))
Inv388 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m <= r) \/ (~(r \in one_a))
Inv389 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m <= r) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv39 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ ((<<n, m, val>> \in vote))
Inv390 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m \in one_a) \/ ((n \in q))
Inv391 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m \in one_a) \/ ((one_a = one_a \cup {r}))
Inv392 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m \in one_a) \/ ((proposal = proposal \cup {<<r, val>>}))
Inv393 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m \in one_a) \/ ((r <= m))
Inv394 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m \in one_a) \/ ((r = None))
Inv395 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m \in one_a) \/ ((r \in one_a))
Inv396 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m \in one_a) \/ ((vote = vote \cup {<<n, r, val>>}))
Inv397 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m \in one_a) \/ (~((m > r)))
Inv398 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m \in one_a) \/ (~((r > m)))
Inv399 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m \in one_a) \/ (~(<<m, val>> \in proposal))
Inv4 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ ((<<n, m>> \in one_b))
Inv40 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ ((<<n, m>> \in left_rnd))
Inv400 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m \in one_a) \/ (~(<<n, m, val>> \in vote))
Inv401 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m \in one_a) \/ (~(<<n, m>> \in left_rnd))
Inv402 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m \in one_a) \/ (~(<<n, m>> \in one_b))
Inv403 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m \in one_a) \/ (~(<<n, r, val>> \in vote))
Inv404 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m \in one_a) \/ (~(<<n, r>> \in left_rnd))
Inv405 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m \in one_a) \/ (~(<<n, r>> \in one_b))
Inv406 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m \in one_a) \/ (~(<<r, val>> \in proposal))
Inv407 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m \in one_a) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv408 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m \in one_a) \/ (~(m <= r))
Inv409 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m \in one_a) \/ (~(n \in q))
Inv41 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ ((<<n, m>> \in one_b))
Inv410 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m \in one_a) \/ (~(one_a = one_a \cup {r}))
Inv411 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m \in one_a) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv412 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m \in one_a) \/ (~(r <= m))
Inv413 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m \in one_a) \/ (~(r = None))
Inv414 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m \in one_a) \/ (~(r \in one_a))
Inv415 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (m \in one_a) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv416 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (n \in q) \/ ((one_a = one_a \cup {r}))
Inv417 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (n \in q) \/ ((proposal = proposal \cup {<<r, val>>}))
Inv418 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (n \in q) \/ ((r <= m))
Inv419 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (n \in q) \/ ((r = None))
Inv42 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ ((<<n, r, val>> \in vote))
Inv420 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (n \in q) \/ ((r \in one_a))
Inv421 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (n \in q) \/ ((vote = vote \cup {<<n, r, val>>}))
Inv422 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (n \in q) \/ (~((m > r)))
Inv423 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (n \in q) \/ (~((r > m)))
Inv424 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (n \in q) \/ (~(<<m, val>> \in proposal))
Inv425 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (n \in q) \/ (~(<<n, m, val>> \in vote))
Inv426 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (n \in q) \/ (~(<<n, m>> \in left_rnd))
Inv427 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (n \in q) \/ (~(<<n, m>> \in one_b))
Inv428 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (n \in q) \/ (~(<<n, r, val>> \in vote))
Inv429 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (n \in q) \/ (~(<<n, r>> \in left_rnd))
Inv43 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ ((<<n, r>> \in left_rnd))
Inv430 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (n \in q) \/ (~(<<n, r>> \in one_b))
Inv431 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (n \in q) \/ (~(<<r, val>> \in proposal))
Inv432 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (n \in q) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv433 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (n \in q) \/ (~(m <= r))
Inv434 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (n \in q) \/ (~(m \in one_a))
Inv435 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (n \in q) \/ (~(one_a = one_a \cup {r}))
Inv436 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (n \in q) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv437 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (n \in q) \/ (~(r <= m))
Inv438 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (n \in q) \/ (~(r = None))
Inv439 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (n \in q) \/ (~(r \in one_a))
Inv44 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ ((<<n, r>> \in one_b))
Inv440 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (n \in q) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv441 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (one_a = one_a \cup {r}) \/ ((proposal = proposal \cup {<<r, val>>}))
Inv442 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (one_a = one_a \cup {r}) \/ ((r <= m))
Inv443 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (one_a = one_a \cup {r}) \/ ((r = None))
Inv444 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (one_a = one_a \cup {r}) \/ ((r \in one_a))
Inv445 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (one_a = one_a \cup {r}) \/ ((vote = vote \cup {<<n, r, val>>}))
Inv446 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (one_a = one_a \cup {r}) \/ (~((m > r)))
Inv447 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (one_a = one_a \cup {r}) \/ (~((r > m)))
Inv448 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (one_a = one_a \cup {r}) \/ (~(<<m, val>> \in proposal))
Inv449 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (one_a = one_a \cup {r}) \/ (~(<<n, m, val>> \in vote))
Inv45 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ ((<<r, val>> \in proposal))
Inv450 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (one_a = one_a \cup {r}) \/ (~(<<n, m>> \in left_rnd))
Inv451 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (one_a = one_a \cup {r}) \/ (~(<<n, m>> \in one_b))
Inv452 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (one_a = one_a \cup {r}) \/ (~(<<n, r, val>> \in vote))
Inv453 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (one_a = one_a \cup {r}) \/ (~(<<n, r>> \in left_rnd))
Inv454 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (one_a = one_a \cup {r}) \/ (~(<<n, r>> \in one_b))
Inv455 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (one_a = one_a \cup {r}) \/ (~(<<r, val>> \in proposal))
Inv456 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (one_a = one_a \cup {r}) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv457 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (one_a = one_a \cup {r}) \/ (~(m <= r))
Inv458 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (one_a = one_a \cup {r}) \/ (~(m \in one_a))
Inv459 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (one_a = one_a \cup {r}) \/ (~(n \in q))
Inv46 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ ((decision = decision \cup {<<n, r, val>>}))
Inv460 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (one_a = one_a \cup {r}) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv461 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (one_a = one_a \cup {r}) \/ (~(r <= m))
Inv462 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (one_a = one_a \cup {r}) \/ (~(r = None))
Inv463 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (one_a = one_a \cup {r}) \/ (~(r \in one_a))
Inv464 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (one_a = one_a \cup {r}) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv465 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (proposal = proposal \cup {<<r, val>>}) \/ ((r <= m))
Inv466 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (proposal = proposal \cup {<<r, val>>}) \/ ((r = None))
Inv467 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (proposal = proposal \cup {<<r, val>>}) \/ ((r \in one_a))
Inv468 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (proposal = proposal \cup {<<r, val>>}) \/ ((vote = vote \cup {<<n, r, val>>}))
Inv469 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (proposal = proposal \cup {<<r, val>>}) \/ (~((m > r)))
Inv47 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ ((m <= r))
Inv470 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (proposal = proposal \cup {<<r, val>>}) \/ (~((r > m)))
Inv471 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (proposal = proposal \cup {<<r, val>>}) \/ (~(<<m, val>> \in proposal))
Inv472 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (proposal = proposal \cup {<<r, val>>}) \/ (~(<<n, m, val>> \in vote))
Inv473 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (proposal = proposal \cup {<<r, val>>}) \/ (~(<<n, m>> \in left_rnd))
Inv474 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (proposal = proposal \cup {<<r, val>>}) \/ (~(<<n, m>> \in one_b))
Inv475 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (proposal = proposal \cup {<<r, val>>}) \/ (~(<<n, r, val>> \in vote))
Inv476 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (proposal = proposal \cup {<<r, val>>}) \/ (~(<<n, r>> \in left_rnd))
Inv477 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (proposal = proposal \cup {<<r, val>>}) \/ (~(<<n, r>> \in one_b))
Inv478 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (proposal = proposal \cup {<<r, val>>}) \/ (~(<<r, val>> \in proposal))
Inv479 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (proposal = proposal \cup {<<r, val>>}) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv48 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ ((m \in one_a))
Inv480 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (proposal = proposal \cup {<<r, val>>}) \/ (~(m <= r))
Inv481 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (proposal = proposal \cup {<<r, val>>}) \/ (~(m \in one_a))
Inv482 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (proposal = proposal \cup {<<r, val>>}) \/ (~(n \in q))
Inv483 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (proposal = proposal \cup {<<r, val>>}) \/ (~(one_a = one_a \cup {r}))
Inv484 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (proposal = proposal \cup {<<r, val>>}) \/ (~(r <= m))
Inv485 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (proposal = proposal \cup {<<r, val>>}) \/ (~(r = None))
Inv486 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (proposal = proposal \cup {<<r, val>>}) \/ (~(r \in one_a))
Inv487 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (proposal = proposal \cup {<<r, val>>}) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv488 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r <= m) \/ ((r = None))
Inv489 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r <= m) \/ ((r \in one_a))
Inv49 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ ((n \in q))
Inv490 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r <= m) \/ ((vote = vote \cup {<<n, r, val>>}))
Inv491 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r <= m) \/ (~((m > r)))
Inv492 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r <= m) \/ (~((r > m)))
Inv493 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r <= m) \/ (~(<<m, val>> \in proposal))
Inv494 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r <= m) \/ (~(<<n, m, val>> \in vote))
Inv495 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r <= m) \/ (~(<<n, m>> \in left_rnd))
Inv496 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r <= m) \/ (~(<<n, m>> \in one_b))
Inv497 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r <= m) \/ (~(<<n, r, val>> \in vote))
Inv498 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r <= m) \/ (~(<<n, r>> \in left_rnd))
Inv499 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r <= m) \/ (~(<<n, r>> \in one_b))
Inv5 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ ((<<n, r, val>> \in vote))
Inv50 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ ((one_a = one_a \cup {r}))
Inv500 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r <= m) \/ (~(<<r, val>> \in proposal))
Inv501 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r <= m) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv502 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r <= m) \/ (~(m <= r))
Inv503 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r <= m) \/ (~(m \in one_a))
Inv504 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r <= m) \/ (~(n \in q))
Inv505 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r <= m) \/ (~(one_a = one_a \cup {r}))
Inv506 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r <= m) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv507 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r <= m) \/ (~(r = None))
Inv508 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r <= m) \/ (~(r \in one_a))
Inv509 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r <= m) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv51 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ ((proposal = proposal \cup {<<r, val>>}))
Inv510 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r = None) \/ ((r \in one_a))
Inv511 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r = None) \/ ((vote = vote \cup {<<n, r, val>>}))
Inv512 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r = None) \/ (~((m > r)))
Inv513 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r = None) \/ (~((r > m)))
Inv514 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r = None) \/ (~(<<m, val>> \in proposal))
Inv515 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r = None) \/ (~(<<n, m, val>> \in vote))
Inv516 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r = None) \/ (~(<<n, m>> \in left_rnd))
Inv517 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r = None) \/ (~(<<n, m>> \in one_b))
Inv518 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r = None) \/ (~(<<n, r, val>> \in vote))
Inv519 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r = None) \/ (~(<<n, r>> \in left_rnd))
Inv52 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ ((r <= m))
Inv520 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r = None) \/ (~(<<n, r>> \in one_b))
Inv521 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r = None) \/ (~(<<r, val>> \in proposal))
Inv522 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r = None) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv523 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r = None) \/ (~(m <= r))
Inv524 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r = None) \/ (~(m \in one_a))
Inv525 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r = None) \/ (~(n \in q))
Inv526 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r = None) \/ (~(one_a = one_a \cup {r}))
Inv527 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r = None) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv528 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r = None) \/ (~(r <= m))
Inv529 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r = None) \/ (~(r \in one_a))
Inv53 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ ((r = None))
Inv530 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r = None) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv531 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r \in one_a) \/ ((vote = vote \cup {<<n, r, val>>}))
Inv532 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r \in one_a) \/ (~((m > r)))
Inv533 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r \in one_a) \/ (~((r > m)))
Inv534 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r \in one_a) \/ (~(<<m, val>> \in proposal))
Inv535 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r \in one_a) \/ (~(<<n, m, val>> \in vote))
Inv536 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r \in one_a) \/ (~(<<n, m>> \in left_rnd))
Inv537 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r \in one_a) \/ (~(<<n, m>> \in one_b))
Inv538 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r \in one_a) \/ (~(<<n, r, val>> \in vote))
Inv539 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r \in one_a) \/ (~(<<n, r>> \in left_rnd))
Inv54 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ ((r \in one_a))
Inv540 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r \in one_a) \/ (~(<<n, r>> \in one_b))
Inv541 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r \in one_a) \/ (~(<<r, val>> \in proposal))
Inv542 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r \in one_a) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv543 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r \in one_a) \/ (~(m <= r))
Inv544 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r \in one_a) \/ (~(m \in one_a))
Inv545 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r \in one_a) \/ (~(n \in q))
Inv546 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r \in one_a) \/ (~(one_a = one_a \cup {r}))
Inv547 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r \in one_a) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv548 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r \in one_a) \/ (~(r <= m))
Inv549 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r \in one_a) \/ (~(r = None))
Inv55 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ ((vote = vote \cup {<<n, r, val>>}))
Inv550 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (r \in one_a) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv551 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (vote = vote \cup {<<n, r, val>>}) \/ (~((m > r)))
Inv552 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (vote = vote \cup {<<n, r, val>>}) \/ (~((r > m)))
Inv553 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (vote = vote \cup {<<n, r, val>>}) \/ (~(<<m, val>> \in proposal))
Inv554 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (vote = vote \cup {<<n, r, val>>}) \/ (~(<<n, m, val>> \in vote))
Inv555 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (vote = vote \cup {<<n, r, val>>}) \/ (~(<<n, m>> \in left_rnd))
Inv556 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (vote = vote \cup {<<n, r, val>>}) \/ (~(<<n, m>> \in one_b))
Inv557 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (vote = vote \cup {<<n, r, val>>}) \/ (~(<<n, r, val>> \in vote))
Inv558 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (vote = vote \cup {<<n, r, val>>}) \/ (~(<<n, r>> \in left_rnd))
Inv559 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (vote = vote \cup {<<n, r, val>>}) \/ (~(<<n, r>> \in one_b))
Inv56 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ (~((m > r)))
Inv560 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (vote = vote \cup {<<n, r, val>>}) \/ (~(<<r, val>> \in proposal))
Inv561 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (vote = vote \cup {<<n, r, val>>}) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv562 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (vote = vote \cup {<<n, r, val>>}) \/ (~(m <= r))
Inv563 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (vote = vote \cup {<<n, r, val>>}) \/ (~(m \in one_a))
Inv564 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (vote = vote \cup {<<n, r, val>>}) \/ (~(n \in q))
Inv565 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (vote = vote \cup {<<n, r, val>>}) \/ (~(one_a = one_a \cup {r}))
Inv566 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (vote = vote \cup {<<n, r, val>>}) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv567 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (vote = vote \cup {<<n, r, val>>}) \/ (~(r <= m))
Inv568 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (vote = vote \cup {<<n, r, val>>}) \/ (~(r = None))
Inv569 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (vote = vote \cup {<<n, r, val>>}) \/ (~(r \in one_a))
Inv57 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ (~(<<m, val>> \in proposal))
Inv570 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((m > r)) \/ (~((r > m)))
Inv571 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((m > r)) \/ (~(<<m, val>> \in proposal))
Inv572 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((m > r)) \/ (~(<<n, m, val>> \in vote))
Inv573 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((m > r)) \/ (~(<<n, m>> \in left_rnd))
Inv574 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((m > r)) \/ (~(<<n, m>> \in one_b))
Inv575 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((m > r)) \/ (~(<<n, r, val>> \in vote))
Inv576 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((m > r)) \/ (~(<<n, r>> \in left_rnd))
Inv577 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((m > r)) \/ (~(<<n, r>> \in one_b))
Inv578 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((m > r)) \/ (~(<<r, val>> \in proposal))
Inv579 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((m > r)) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv58 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ (~(<<n, m, val>> \in vote))
Inv580 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((m > r)) \/ (~(m <= r))
Inv581 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((m > r)) \/ (~(m \in one_a))
Inv582 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((m > r)) \/ (~(n \in q))
Inv583 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((m > r)) \/ (~(one_a = one_a \cup {r}))
Inv584 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((m > r)) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv585 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((m > r)) \/ (~(r <= m))
Inv586 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((m > r)) \/ (~(r = None))
Inv587 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((m > r)) \/ (~(r \in one_a))
Inv588 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((m > r)) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv589 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((r > m)) \/ (~(<<m, val>> \in proposal))
Inv59 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ (~(<<n, m>> \in left_rnd))
Inv590 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((r > m)) \/ (~(<<n, m, val>> \in vote))
Inv591 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((r > m)) \/ (~(<<n, m>> \in left_rnd))
Inv592 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((r > m)) \/ (~(<<n, m>> \in one_b))
Inv593 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((r > m)) \/ (~(<<n, r, val>> \in vote))
Inv594 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((r > m)) \/ (~(<<n, r>> \in left_rnd))
Inv595 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((r > m)) \/ (~(<<n, r>> \in one_b))
Inv596 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((r > m)) \/ (~(<<r, val>> \in proposal))
Inv597 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((r > m)) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv598 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((r > m)) \/ (~(m <= r))
Inv599 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((r > m)) \/ (~(m \in one_a))
Inv6 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ ((<<n, r>> \in left_rnd))
Inv60 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ (~(<<n, m>> \in one_b))
Inv600 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((r > m)) \/ (~(n \in q))
Inv601 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((r > m)) \/ (~(one_a = one_a \cup {r}))
Inv602 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((r > m)) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv603 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((r > m)) \/ (~(r <= m))
Inv604 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((r > m)) \/ (~(r = None))
Inv605 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((r > m)) \/ (~(r \in one_a))
Inv606 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~((r > m)) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv607 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<m, val>> \in proposal) \/ (~(<<n, m, val>> \in vote))
Inv608 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<m, val>> \in proposal) \/ (~(<<n, m>> \in left_rnd))
Inv609 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<m, val>> \in proposal) \/ (~(<<n, m>> \in one_b))
Inv61 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ (~(<<n, r, val>> \in vote))
Inv610 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<m, val>> \in proposal) \/ (~(<<n, r, val>> \in vote))
Inv611 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<m, val>> \in proposal) \/ (~(<<n, r>> \in left_rnd))
Inv612 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<m, val>> \in proposal) \/ (~(<<n, r>> \in one_b))
Inv613 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<m, val>> \in proposal) \/ (~(<<r, val>> \in proposal))
Inv614 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<m, val>> \in proposal) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv615 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<m, val>> \in proposal) \/ (~(m <= r))
Inv616 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<m, val>> \in proposal) \/ (~(m \in one_a))
Inv617 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<m, val>> \in proposal) \/ (~(n \in q))
Inv618 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<m, val>> \in proposal) \/ (~(one_a = one_a \cup {r}))
Inv619 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<m, val>> \in proposal) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv62 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ (~(<<n, r>> \in left_rnd))
Inv620 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<m, val>> \in proposal) \/ (~(r <= m))
Inv621 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<m, val>> \in proposal) \/ (~(r = None))
Inv622 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<m, val>> \in proposal) \/ (~(r \in one_a))
Inv623 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<m, val>> \in proposal) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv624 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m, val>> \in vote) \/ (~(<<n, m>> \in left_rnd))
Inv625 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m, val>> \in vote) \/ (~(<<n, m>> \in one_b))
Inv626 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m, val>> \in vote) \/ (~(<<n, r, val>> \in vote))
Inv627 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m, val>> \in vote) \/ (~(<<n, r>> \in left_rnd))
Inv628 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m, val>> \in vote) \/ (~(<<n, r>> \in one_b))
Inv629 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m, val>> \in vote) \/ (~(<<r, val>> \in proposal))
Inv63 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ (~(<<n, r>> \in one_b))
Inv630 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m, val>> \in vote) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv631 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m, val>> \in vote) \/ (~(m <= r))
Inv632 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m, val>> \in vote) \/ (~(m \in one_a))
Inv633 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m, val>> \in vote) \/ (~(n \in q))
Inv634 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m, val>> \in vote) \/ (~(one_a = one_a \cup {r}))
Inv635 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m, val>> \in vote) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv636 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m, val>> \in vote) \/ (~(r <= m))
Inv637 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m, val>> \in vote) \/ (~(r = None))
Inv638 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m, val>> \in vote) \/ (~(r \in one_a))
Inv639 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m, val>> \in vote) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv64 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ (~(<<r, val>> \in proposal))
Inv640 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in left_rnd) \/ (~(<<n, m>> \in one_b))
Inv641 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in left_rnd) \/ (~(<<n, r, val>> \in vote))
Inv642 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in left_rnd) \/ (~(<<n, r>> \in left_rnd))
Inv643 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in left_rnd) \/ (~(<<n, r>> \in one_b))
Inv644 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in left_rnd) \/ (~(<<r, val>> \in proposal))
Inv645 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in left_rnd) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv646 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in left_rnd) \/ (~(m <= r))
Inv647 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in left_rnd) \/ (~(m \in one_a))
Inv648 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in left_rnd) \/ (~(n \in q))
Inv649 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in left_rnd) \/ (~(one_a = one_a \cup {r}))
Inv65 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv650 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in left_rnd) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv651 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in left_rnd) \/ (~(r <= m))
Inv652 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in left_rnd) \/ (~(r = None))
Inv653 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in left_rnd) \/ (~(r \in one_a))
Inv654 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in left_rnd) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv655 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in one_b) \/ (~(<<n, r, val>> \in vote))
Inv656 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in one_b) \/ (~(<<n, r>> \in left_rnd))
Inv657 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in one_b) \/ (~(<<n, r>> \in one_b))
Inv658 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in one_b) \/ (~(<<r, val>> \in proposal))
Inv659 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in one_b) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv66 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ (~(m <= r))
Inv660 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in one_b) \/ (~(m <= r))
Inv661 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in one_b) \/ (~(m \in one_a))
Inv662 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in one_b) \/ (~(n \in q))
Inv663 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in one_b) \/ (~(one_a = one_a \cup {r}))
Inv664 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in one_b) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv665 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in one_b) \/ (~(r <= m))
Inv666 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in one_b) \/ (~(r = None))
Inv667 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in one_b) \/ (~(r \in one_a))
Inv668 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, m>> \in one_b) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv669 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r, val>> \in vote) \/ (~(<<n, r>> \in left_rnd))
Inv67 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ (~(m \in one_a))
Inv670 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r, val>> \in vote) \/ (~(<<n, r>> \in one_b))
Inv671 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r, val>> \in vote) \/ (~(<<r, val>> \in proposal))
Inv672 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r, val>> \in vote) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv673 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r, val>> \in vote) \/ (~(m <= r))
Inv674 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r, val>> \in vote) \/ (~(m \in one_a))
Inv675 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r, val>> \in vote) \/ (~(n \in q))
Inv676 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r, val>> \in vote) \/ (~(one_a = one_a \cup {r}))
Inv677 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r, val>> \in vote) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv678 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r, val>> \in vote) \/ (~(r <= m))
Inv679 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r, val>> \in vote) \/ (~(r = None))
Inv68 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ (~(n \in q))
Inv680 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r, val>> \in vote) \/ (~(r \in one_a))
Inv681 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r, val>> \in vote) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv682 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r>> \in left_rnd) \/ (~(<<n, r>> \in one_b))
Inv683 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r>> \in left_rnd) \/ (~(<<r, val>> \in proposal))
Inv684 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r>> \in left_rnd) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv685 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r>> \in left_rnd) \/ (~(m <= r))
Inv686 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r>> \in left_rnd) \/ (~(m \in one_a))
Inv687 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r>> \in left_rnd) \/ (~(n \in q))
Inv688 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r>> \in left_rnd) \/ (~(one_a = one_a \cup {r}))
Inv689 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r>> \in left_rnd) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv69 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ (~(one_a = one_a \cup {r}))
Inv690 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r>> \in left_rnd) \/ (~(r <= m))
Inv691 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r>> \in left_rnd) \/ (~(r = None))
Inv692 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r>> \in left_rnd) \/ (~(r \in one_a))
Inv693 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r>> \in left_rnd) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv694 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r>> \in one_b) \/ (~(<<r, val>> \in proposal))
Inv695 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r>> \in one_b) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv696 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r>> \in one_b) \/ (~(m <= r))
Inv697 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r>> \in one_b) \/ (~(m \in one_a))
Inv698 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r>> \in one_b) \/ (~(n \in q))
Inv699 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r>> \in one_b) \/ (~(one_a = one_a \cup {r}))
Inv7 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ ((<<n, r>> \in one_b))
Inv70 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv700 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r>> \in one_b) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv701 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r>> \in one_b) \/ (~(r <= m))
Inv702 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r>> \in one_b) \/ (~(r = None))
Inv703 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r>> \in one_b) \/ (~(r \in one_a))
Inv704 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<n, r>> \in one_b) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv705 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<r, val>> \in proposal) \/ (~(decision = decision \cup {<<n, r, val>>}))
Inv706 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<r, val>> \in proposal) \/ (~(m <= r))
Inv707 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<r, val>> \in proposal) \/ (~(m \in one_a))
Inv708 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<r, val>> \in proposal) \/ (~(n \in q))
Inv709 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<r, val>> \in proposal) \/ (~(one_a = one_a \cup {r}))
Inv71 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ (~(r <= m))
Inv710 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<r, val>> \in proposal) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv711 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<r, val>> \in proposal) \/ (~(r <= m))
Inv712 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<r, val>> \in proposal) \/ (~(r = None))
Inv713 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<r, val>> \in proposal) \/ (~(r \in one_a))
Inv714 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(<<r, val>> \in proposal) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv715 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(decision = decision \cup {<<n, r, val>>}) \/ (~(m <= r))
Inv716 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(decision = decision \cup {<<n, r, val>>}) \/ (~(m \in one_a))
Inv717 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(decision = decision \cup {<<n, r, val>>}) \/ (~(n \in q))
Inv718 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(decision = decision \cup {<<n, r, val>>}) \/ (~(one_a = one_a \cup {r}))
Inv719 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(decision = decision \cup {<<n, r, val>>}) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv72 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ (~(r = None))
Inv720 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(decision = decision \cup {<<n, r, val>>}) \/ (~(r <= m))
Inv721 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(decision = decision \cup {<<n, r, val>>}) \/ (~(r = None))
Inv722 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(decision = decision \cup {<<n, r, val>>}) \/ (~(r \in one_a))
Inv723 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(decision = decision \cup {<<n, r, val>>}) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv724 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(m <= r) \/ (~(m \in one_a))
Inv725 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(m <= r) \/ (~(n \in q))
Inv726 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(m <= r) \/ (~(one_a = one_a \cup {r}))
Inv727 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(m <= r) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv728 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(m <= r) \/ (~(r <= m))
Inv729 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(m <= r) \/ (~(r = None))
Inv73 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ (~(r \in one_a))
Inv730 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(m <= r) \/ (~(r \in one_a))
Inv731 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(m <= r) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv732 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(m \in one_a) \/ (~(n \in q))
Inv733 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(m \in one_a) \/ (~(one_a = one_a \cup {r}))
Inv734 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(m \in one_a) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv735 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(m \in one_a) \/ (~(r <= m))
Inv736 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(m \in one_a) \/ (~(r = None))
Inv737 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(m \in one_a) \/ (~(r \in one_a))
Inv738 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(m \in one_a) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv739 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(n \in q) \/ (~(one_a = one_a \cup {r}))
Inv74 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((r > m)) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv740 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(n \in q) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv741 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(n \in q) \/ (~(r <= m))
Inv742 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(n \in q) \/ (~(r = None))
Inv743 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(n \in q) \/ (~(r \in one_a))
Inv744 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(n \in q) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv745 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(one_a = one_a \cup {r}) \/ (~(proposal = proposal \cup {<<r, val>>}))
Inv746 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(one_a = one_a \cup {r}) \/ (~(r <= m))
Inv747 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(one_a = one_a \cup {r}) \/ (~(r = None))
Inv748 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(one_a = one_a \cup {r}) \/ (~(r \in one_a))
Inv749 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(one_a = one_a \cup {r}) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv75 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ ((<<n, m, val>> \in vote))
Inv750 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(proposal = proposal \cup {<<r, val>>}) \/ (~(r <= m))
Inv751 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(proposal = proposal \cup {<<r, val>>}) \/ (~(r = None))
Inv752 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(proposal = proposal \cup {<<r, val>>}) \/ (~(r \in one_a))
Inv753 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(proposal = proposal \cup {<<r, val>>}) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv754 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(r <= m) \/ (~(r = None))
Inv755 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(r <= m) \/ (~(r \in one_a))
Inv756 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(r <= m) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv757 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(r = None) \/ (~(r \in one_a))
Inv758 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(r = None) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv759 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ~(r \in one_a) \/ (~(vote = vote \cup {<<n, r, val>>}))
Inv76 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ ((<<n, m>> \in left_rnd))
Inv77 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ ((<<n, m>> \in one_b))
Inv78 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ ((<<n, r, val>> \in vote))
Inv79 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ ((<<n, r>> \in left_rnd))
Inv8 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ ((<<r, val>> \in proposal))
Inv80 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ ((<<n, r>> \in one_b))
Inv81 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ ((<<r, val>> \in proposal))
Inv82 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ ((decision = decision \cup {<<n, r, val>>}))
Inv83 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ ((m <= r))
Inv84 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ ((m \in one_a))
Inv85 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ ((n \in q))
Inv86 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ ((one_a = one_a \cup {r}))
Inv87 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ ((proposal = proposal \cup {<<r, val>>}))
Inv88 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ ((r <= m))
Inv89 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ ((r = None))
Inv9 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : ((m > r)) \/ ((decision = decision \cup {<<n, r, val>>}))
Inv90 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ ((r \in one_a))
Inv91 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ ((vote = vote \cup {<<n, r, val>>}))
Inv92 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ (~((m > r)))
Inv93 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ (~((r > m)))
Inv94 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ (~(<<n, m, val>> \in vote))
Inv95 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ (~(<<n, m>> \in left_rnd))
Inv96 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ (~(<<n, m>> \in one_b))
Inv97 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ (~(<<n, r, val>> \in vote))
Inv98 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ (~(<<n, r>> \in left_rnd))
Inv99 == \A r \in Round : \A n \in Node : \A val \in Value : \A q \in Quorum : \E m \in Round : (<<m, val>> \in proposal) \/ (~(<<n, r>> \in one_b))

kCTIs == 
	\/ /\ left_rnd = {<<a1, 0>>, <<a1, 1>>, <<a2, 0>>, <<a2, 1>>, <<a3, 0>>} /\ one_a = {} /\ one_b = {{<<a1, 0>>, <<a3, 1>>}, {<<a1, 0>>, <<a2, 0>>, <<a2, 1>>, <<a3, 0>>}} /\ one_b_max_vote = { <<a1, 0, 0, v2>>,   <<a1, 0, 1, v1>>,   <<a1, 1, 0, v1>>,   <<a1, 1, 0, v2>>,   <<a1, 1, 1, v1>>,   <<a2, 0, 0, v2>>,   <<a2, 0, 1, v1>>,   <<a3, 0, 0, v2>>,   <<a3, 0, 1, v2>>,   <<a3, 1, 0, v2>>,   <<a3, 1, 1, v1>>,   <<a3, 1, 1, v2>> } /\ decision = {<<a1, 1, v1>>, <<a2, 0, v1>>, <<a3, 0, v1>>, <<a3, 1, v1>>} /\ vote = {<<a1, 0, v1>>, <<a2, 0, v2>>, <<a2, 1, v1>>, <<a3, 1, v1>>, <<a3, 1, v2>>} /\ proposal = {<<1, v1>>}
	   /\ ctiId = "2561106814639505156"


InvVals ==
	    /\ TRUE
	   /\ Inv0_val = Inv0
	   /\ Inv1_val = Inv1
	   /\ Inv10_val = Inv10
	   /\ Inv100_val = Inv100
	   /\ Inv101_val = Inv101
	   /\ Inv102_val = Inv102
	   /\ Inv103_val = Inv103
	   /\ Inv104_val = Inv104
	   /\ Inv105_val = Inv105
	   /\ Inv106_val = Inv106
	   /\ Inv107_val = Inv107
	   /\ Inv108_val = Inv108
	   /\ Inv109_val = Inv109
	   /\ Inv11_val = Inv11
	   /\ Inv110_val = Inv110
	   /\ Inv111_val = Inv111
	   /\ Inv112_val = Inv112
	   /\ Inv113_val = Inv113
	   /\ Inv114_val = Inv114
	   /\ Inv115_val = Inv115
	   /\ Inv116_val = Inv116
	   /\ Inv117_val = Inv117
	   /\ Inv118_val = Inv118
	   /\ Inv119_val = Inv119
	   /\ Inv12_val = Inv12
	   /\ Inv120_val = Inv120
	   /\ Inv121_val = Inv121
	   /\ Inv122_val = Inv122
	   /\ Inv123_val = Inv123
	   /\ Inv124_val = Inv124
	   /\ Inv125_val = Inv125
	   /\ Inv126_val = Inv126
	   /\ Inv127_val = Inv127
	   /\ Inv128_val = Inv128
	   /\ Inv129_val = Inv129
	   /\ Inv13_val = Inv13
	   /\ Inv130_val = Inv130
	   /\ Inv131_val = Inv131
	   /\ Inv132_val = Inv132
	   /\ Inv133_val = Inv133
	   /\ Inv134_val = Inv134
	   /\ Inv135_val = Inv135
	   /\ Inv136_val = Inv136
	   /\ Inv137_val = Inv137
	   /\ Inv138_val = Inv138
	   /\ Inv139_val = Inv139
	   /\ Inv14_val = Inv14
	   /\ Inv140_val = Inv140
	   /\ Inv141_val = Inv141
	   /\ Inv142_val = Inv142
	   /\ Inv143_val = Inv143
	   /\ Inv144_val = Inv144
	   /\ Inv145_val = Inv145
	   /\ Inv146_val = Inv146
	   /\ Inv147_val = Inv147
	   /\ Inv148_val = Inv148
	   /\ Inv149_val = Inv149
	   /\ Inv15_val = Inv15
	   /\ Inv150_val = Inv150
	   /\ Inv151_val = Inv151
	   /\ Inv152_val = Inv152
	   /\ Inv153_val = Inv153
	   /\ Inv154_val = Inv154
	   /\ Inv155_val = Inv155
	   /\ Inv156_val = Inv156
	   /\ Inv157_val = Inv157
	   /\ Inv158_val = Inv158
	   /\ Inv159_val = Inv159
	   /\ Inv16_val = Inv16
	   /\ Inv160_val = Inv160
	   /\ Inv161_val = Inv161
	   /\ Inv162_val = Inv162
	   /\ Inv163_val = Inv163
	   /\ Inv164_val = Inv164
	   /\ Inv165_val = Inv165
	   /\ Inv166_val = Inv166
	   /\ Inv167_val = Inv167
	   /\ Inv168_val = Inv168
	   /\ Inv169_val = Inv169
	   /\ Inv17_val = Inv17
	   /\ Inv170_val = Inv170
	   /\ Inv171_val = Inv171
	   /\ Inv172_val = Inv172
	   /\ Inv173_val = Inv173
	   /\ Inv174_val = Inv174
	   /\ Inv175_val = Inv175
	   /\ Inv176_val = Inv176
	   /\ Inv177_val = Inv177
	   /\ Inv178_val = Inv178
	   /\ Inv179_val = Inv179
	   /\ Inv18_val = Inv18
	   /\ Inv180_val = Inv180
	   /\ Inv181_val = Inv181
	   /\ Inv182_val = Inv182
	   /\ Inv183_val = Inv183
	   /\ Inv184_val = Inv184
	   /\ Inv185_val = Inv185
	   /\ Inv186_val = Inv186
	   /\ Inv187_val = Inv187
	   /\ Inv188_val = Inv188
	   /\ Inv189_val = Inv189
	   /\ Inv19_val = Inv19
	   /\ Inv190_val = Inv190
	   /\ Inv191_val = Inv191
	   /\ Inv192_val = Inv192
	   /\ Inv193_val = Inv193
	   /\ Inv194_val = Inv194
	   /\ Inv195_val = Inv195
	   /\ Inv196_val = Inv196
	   /\ Inv197_val = Inv197
	   /\ Inv198_val = Inv198
	   /\ Inv199_val = Inv199
	   /\ Inv2_val = Inv2
	   /\ Inv20_val = Inv20
	   /\ Inv200_val = Inv200
	   /\ Inv201_val = Inv201
	   /\ Inv202_val = Inv202
	   /\ Inv203_val = Inv203
	   /\ Inv204_val = Inv204
	   /\ Inv205_val = Inv205
	   /\ Inv206_val = Inv206
	   /\ Inv207_val = Inv207
	   /\ Inv208_val = Inv208
	   /\ Inv209_val = Inv209
	   /\ Inv21_val = Inv21
	   /\ Inv210_val = Inv210
	   /\ Inv211_val = Inv211
	   /\ Inv212_val = Inv212
	   /\ Inv213_val = Inv213
	   /\ Inv214_val = Inv214
	   /\ Inv215_val = Inv215
	   /\ Inv216_val = Inv216
	   /\ Inv217_val = Inv217
	   /\ Inv218_val = Inv218
	   /\ Inv219_val = Inv219
	   /\ Inv22_val = Inv22
	   /\ Inv220_val = Inv220
	   /\ Inv221_val = Inv221
	   /\ Inv222_val = Inv222
	   /\ Inv223_val = Inv223
	   /\ Inv224_val = Inv224
	   /\ Inv225_val = Inv225
	   /\ Inv226_val = Inv226
	   /\ Inv227_val = Inv227
	   /\ Inv228_val = Inv228
	   /\ Inv229_val = Inv229
	   /\ Inv23_val = Inv23
	   /\ Inv230_val = Inv230
	   /\ Inv231_val = Inv231
	   /\ Inv232_val = Inv232
	   /\ Inv233_val = Inv233
	   /\ Inv234_val = Inv234
	   /\ Inv235_val = Inv235
	   /\ Inv236_val = Inv236
	   /\ Inv237_val = Inv237
	   /\ Inv238_val = Inv238
	   /\ Inv239_val = Inv239
	   /\ Inv24_val = Inv24
	   /\ Inv240_val = Inv240
	   /\ Inv241_val = Inv241
	   /\ Inv242_val = Inv242
	   /\ Inv243_val = Inv243
	   /\ Inv244_val = Inv244
	   /\ Inv245_val = Inv245
	   /\ Inv246_val = Inv246
	   /\ Inv247_val = Inv247
	   /\ Inv248_val = Inv248
	   /\ Inv249_val = Inv249
	   /\ Inv25_val = Inv25
	   /\ Inv250_val = Inv250
	   /\ Inv251_val = Inv251
	   /\ Inv252_val = Inv252
	   /\ Inv253_val = Inv253
	   /\ Inv254_val = Inv254
	   /\ Inv255_val = Inv255
	   /\ Inv256_val = Inv256
	   /\ Inv257_val = Inv257
	   /\ Inv258_val = Inv258
	   /\ Inv259_val = Inv259
	   /\ Inv26_val = Inv26
	   /\ Inv260_val = Inv260
	   /\ Inv261_val = Inv261
	   /\ Inv262_val = Inv262
	   /\ Inv263_val = Inv263
	   /\ Inv264_val = Inv264
	   /\ Inv265_val = Inv265
	   /\ Inv266_val = Inv266
	   /\ Inv267_val = Inv267
	   /\ Inv268_val = Inv268
	   /\ Inv269_val = Inv269
	   /\ Inv27_val = Inv27
	   /\ Inv270_val = Inv270
	   /\ Inv271_val = Inv271
	   /\ Inv272_val = Inv272
	   /\ Inv273_val = Inv273
	   /\ Inv274_val = Inv274
	   /\ Inv275_val = Inv275
	   /\ Inv276_val = Inv276
	   /\ Inv277_val = Inv277
	   /\ Inv278_val = Inv278
	   /\ Inv279_val = Inv279
	   /\ Inv28_val = Inv28
	   /\ Inv280_val = Inv280
	   /\ Inv281_val = Inv281
	   /\ Inv282_val = Inv282
	   /\ Inv283_val = Inv283
	   /\ Inv284_val = Inv284
	   /\ Inv285_val = Inv285
	   /\ Inv286_val = Inv286
	   /\ Inv287_val = Inv287
	   /\ Inv288_val = Inv288
	   /\ Inv289_val = Inv289
	   /\ Inv29_val = Inv29
	   /\ Inv290_val = Inv290
	   /\ Inv291_val = Inv291
	   /\ Inv292_val = Inv292
	   /\ Inv293_val = Inv293
	   /\ Inv294_val = Inv294
	   /\ Inv295_val = Inv295
	   /\ Inv296_val = Inv296
	   /\ Inv297_val = Inv297
	   /\ Inv298_val = Inv298
	   /\ Inv299_val = Inv299
	   /\ Inv3_val = Inv3
	   /\ Inv30_val = Inv30
	   /\ Inv300_val = Inv300
	   /\ Inv301_val = Inv301
	   /\ Inv302_val = Inv302
	   /\ Inv303_val = Inv303
	   /\ Inv304_val = Inv304
	   /\ Inv305_val = Inv305
	   /\ Inv306_val = Inv306
	   /\ Inv307_val = Inv307
	   /\ Inv308_val = Inv308
	   /\ Inv309_val = Inv309
	   /\ Inv31_val = Inv31
	   /\ Inv310_val = Inv310
	   /\ Inv311_val = Inv311
	   /\ Inv312_val = Inv312
	   /\ Inv313_val = Inv313
	   /\ Inv314_val = Inv314
	   /\ Inv315_val = Inv315
	   /\ Inv316_val = Inv316
	   /\ Inv317_val = Inv317
	   /\ Inv318_val = Inv318
	   /\ Inv319_val = Inv319
	   /\ Inv32_val = Inv32
	   /\ Inv320_val = Inv320
	   /\ Inv321_val = Inv321
	   /\ Inv322_val = Inv322
	   /\ Inv323_val = Inv323
	   /\ Inv324_val = Inv324
	   /\ Inv325_val = Inv325
	   /\ Inv326_val = Inv326
	   /\ Inv327_val = Inv327
	   /\ Inv328_val = Inv328
	   /\ Inv329_val = Inv329
	   /\ Inv33_val = Inv33
	   /\ Inv330_val = Inv330
	   /\ Inv331_val = Inv331
	   /\ Inv332_val = Inv332
	   /\ Inv333_val = Inv333
	   /\ Inv334_val = Inv334
	   /\ Inv335_val = Inv335
	   /\ Inv336_val = Inv336
	   /\ Inv337_val = Inv337
	   /\ Inv338_val = Inv338
	   /\ Inv339_val = Inv339
	   /\ Inv34_val = Inv34
	   /\ Inv340_val = Inv340
	   /\ Inv341_val = Inv341
	   /\ Inv342_val = Inv342
	   /\ Inv343_val = Inv343
	   /\ Inv344_val = Inv344
	   /\ Inv345_val = Inv345
	   /\ Inv346_val = Inv346
	   /\ Inv347_val = Inv347
	   /\ Inv348_val = Inv348
	   /\ Inv349_val = Inv349
	   /\ Inv35_val = Inv35
	   /\ Inv350_val = Inv350
	   /\ Inv351_val = Inv351
	   /\ Inv352_val = Inv352
	   /\ Inv353_val = Inv353
	   /\ Inv354_val = Inv354
	   /\ Inv355_val = Inv355
	   /\ Inv356_val = Inv356
	   /\ Inv357_val = Inv357
	   /\ Inv358_val = Inv358
	   /\ Inv359_val = Inv359
	   /\ Inv36_val = Inv36
	   /\ Inv360_val = Inv360
	   /\ Inv361_val = Inv361
	   /\ Inv362_val = Inv362
	   /\ Inv363_val = Inv363
	   /\ Inv364_val = Inv364
	   /\ Inv365_val = Inv365
	   /\ Inv366_val = Inv366
	   /\ Inv367_val = Inv367
	   /\ Inv368_val = Inv368
	   /\ Inv369_val = Inv369
	   /\ Inv37_val = Inv37
	   /\ Inv370_val = Inv370
	   /\ Inv371_val = Inv371
	   /\ Inv372_val = Inv372
	   /\ Inv373_val = Inv373
	   /\ Inv374_val = Inv374
	   /\ Inv375_val = Inv375
	   /\ Inv376_val = Inv376
	   /\ Inv377_val = Inv377
	   /\ Inv378_val = Inv378
	   /\ Inv379_val = Inv379
	   /\ Inv38_val = Inv38
	   /\ Inv380_val = Inv380
	   /\ Inv381_val = Inv381
	   /\ Inv382_val = Inv382
	   /\ Inv383_val = Inv383
	   /\ Inv384_val = Inv384
	   /\ Inv385_val = Inv385
	   /\ Inv386_val = Inv386
	   /\ Inv387_val = Inv387
	   /\ Inv388_val = Inv388
	   /\ Inv389_val = Inv389
	   /\ Inv39_val = Inv39
	   /\ Inv390_val = Inv390
	   /\ Inv391_val = Inv391
	   /\ Inv392_val = Inv392
	   /\ Inv393_val = Inv393
	   /\ Inv394_val = Inv394
	   /\ Inv395_val = Inv395
	   /\ Inv396_val = Inv396
	   /\ Inv397_val = Inv397
	   /\ Inv398_val = Inv398
	   /\ Inv399_val = Inv399
	   /\ Inv4_val = Inv4
	   /\ Inv40_val = Inv40
	   /\ Inv400_val = Inv400
	   /\ Inv401_val = Inv401
	   /\ Inv402_val = Inv402
	   /\ Inv403_val = Inv403
	   /\ Inv404_val = Inv404
	   /\ Inv405_val = Inv405
	   /\ Inv406_val = Inv406
	   /\ Inv407_val = Inv407
	   /\ Inv408_val = Inv408
	   /\ Inv409_val = Inv409
	   /\ Inv41_val = Inv41
	   /\ Inv410_val = Inv410
	   /\ Inv411_val = Inv411
	   /\ Inv412_val = Inv412
	   /\ Inv413_val = Inv413
	   /\ Inv414_val = Inv414
	   /\ Inv415_val = Inv415
	   /\ Inv416_val = Inv416
	   /\ Inv417_val = Inv417
	   /\ Inv418_val = Inv418
	   /\ Inv419_val = Inv419
	   /\ Inv42_val = Inv42
	   /\ Inv420_val = Inv420
	   /\ Inv421_val = Inv421
	   /\ Inv422_val = Inv422
	   /\ Inv423_val = Inv423
	   /\ Inv424_val = Inv424
	   /\ Inv425_val = Inv425
	   /\ Inv426_val = Inv426
	   /\ Inv427_val = Inv427
	   /\ Inv428_val = Inv428
	   /\ Inv429_val = Inv429
	   /\ Inv43_val = Inv43
	   /\ Inv430_val = Inv430
	   /\ Inv431_val = Inv431
	   /\ Inv432_val = Inv432
	   /\ Inv433_val = Inv433
	   /\ Inv434_val = Inv434
	   /\ Inv435_val = Inv435
	   /\ Inv436_val = Inv436
	   /\ Inv437_val = Inv437
	   /\ Inv438_val = Inv438
	   /\ Inv439_val = Inv439
	   /\ Inv44_val = Inv44
	   /\ Inv440_val = Inv440
	   /\ Inv441_val = Inv441
	   /\ Inv442_val = Inv442
	   /\ Inv443_val = Inv443
	   /\ Inv444_val = Inv444
	   /\ Inv445_val = Inv445
	   /\ Inv446_val = Inv446
	   /\ Inv447_val = Inv447
	   /\ Inv448_val = Inv448
	   /\ Inv449_val = Inv449
	   /\ Inv45_val = Inv45
	   /\ Inv450_val = Inv450
	   /\ Inv451_val = Inv451
	   /\ Inv452_val = Inv452
	   /\ Inv453_val = Inv453
	   /\ Inv454_val = Inv454
	   /\ Inv455_val = Inv455
	   /\ Inv456_val = Inv456
	   /\ Inv457_val = Inv457
	   /\ Inv458_val = Inv458
	   /\ Inv459_val = Inv459
	   /\ Inv46_val = Inv46
	   /\ Inv460_val = Inv460
	   /\ Inv461_val = Inv461
	   /\ Inv462_val = Inv462
	   /\ Inv463_val = Inv463
	   /\ Inv464_val = Inv464
	   /\ Inv465_val = Inv465
	   /\ Inv466_val = Inv466
	   /\ Inv467_val = Inv467
	   /\ Inv468_val = Inv468
	   /\ Inv469_val = Inv469
	   /\ Inv47_val = Inv47
	   /\ Inv470_val = Inv470
	   /\ Inv471_val = Inv471
	   /\ Inv472_val = Inv472
	   /\ Inv473_val = Inv473
	   /\ Inv474_val = Inv474
	   /\ Inv475_val = Inv475
	   /\ Inv476_val = Inv476
	   /\ Inv477_val = Inv477
	   /\ Inv478_val = Inv478
	   /\ Inv479_val = Inv479
	   /\ Inv48_val = Inv48
	   /\ Inv480_val = Inv480
	   /\ Inv481_val = Inv481
	   /\ Inv482_val = Inv482
	   /\ Inv483_val = Inv483
	   /\ Inv484_val = Inv484
	   /\ Inv485_val = Inv485
	   /\ Inv486_val = Inv486
	   /\ Inv487_val = Inv487
	   /\ Inv488_val = Inv488
	   /\ Inv489_val = Inv489
	   /\ Inv49_val = Inv49
	   /\ Inv490_val = Inv490
	   /\ Inv491_val = Inv491
	   /\ Inv492_val = Inv492
	   /\ Inv493_val = Inv493
	   /\ Inv494_val = Inv494
	   /\ Inv495_val = Inv495
	   /\ Inv496_val = Inv496
	   /\ Inv497_val = Inv497
	   /\ Inv498_val = Inv498
	   /\ Inv499_val = Inv499
	   /\ Inv5_val = Inv5
	   /\ Inv50_val = Inv50
	   /\ Inv500_val = Inv500
	   /\ Inv501_val = Inv501
	   /\ Inv502_val = Inv502
	   /\ Inv503_val = Inv503
	   /\ Inv504_val = Inv504
	   /\ Inv505_val = Inv505
	   /\ Inv506_val = Inv506
	   /\ Inv507_val = Inv507
	   /\ Inv508_val = Inv508
	   /\ Inv509_val = Inv509
	   /\ Inv51_val = Inv51
	   /\ Inv510_val = Inv510
	   /\ Inv511_val = Inv511
	   /\ Inv512_val = Inv512
	   /\ Inv513_val = Inv513
	   /\ Inv514_val = Inv514
	   /\ Inv515_val = Inv515
	   /\ Inv516_val = Inv516
	   /\ Inv517_val = Inv517
	   /\ Inv518_val = Inv518
	   /\ Inv519_val = Inv519
	   /\ Inv52_val = Inv52
	   /\ Inv520_val = Inv520
	   /\ Inv521_val = Inv521
	   /\ Inv522_val = Inv522
	   /\ Inv523_val = Inv523
	   /\ Inv524_val = Inv524
	   /\ Inv525_val = Inv525
	   /\ Inv526_val = Inv526
	   /\ Inv527_val = Inv527
	   /\ Inv528_val = Inv528
	   /\ Inv529_val = Inv529
	   /\ Inv53_val = Inv53
	   /\ Inv530_val = Inv530
	   /\ Inv531_val = Inv531
	   /\ Inv532_val = Inv532
	   /\ Inv533_val = Inv533
	   /\ Inv534_val = Inv534
	   /\ Inv535_val = Inv535
	   /\ Inv536_val = Inv536
	   /\ Inv537_val = Inv537
	   /\ Inv538_val = Inv538
	   /\ Inv539_val = Inv539
	   /\ Inv54_val = Inv54
	   /\ Inv540_val = Inv540
	   /\ Inv541_val = Inv541
	   /\ Inv542_val = Inv542
	   /\ Inv543_val = Inv543
	   /\ Inv544_val = Inv544
	   /\ Inv545_val = Inv545
	   /\ Inv546_val = Inv546
	   /\ Inv547_val = Inv547
	   /\ Inv548_val = Inv548
	   /\ Inv549_val = Inv549
	   /\ Inv55_val = Inv55
	   /\ Inv550_val = Inv550
	   /\ Inv551_val = Inv551
	   /\ Inv552_val = Inv552
	   /\ Inv553_val = Inv553
	   /\ Inv554_val = Inv554
	   /\ Inv555_val = Inv555
	   /\ Inv556_val = Inv556
	   /\ Inv557_val = Inv557
	   /\ Inv558_val = Inv558
	   /\ Inv559_val = Inv559
	   /\ Inv56_val = Inv56
	   /\ Inv560_val = Inv560
	   /\ Inv561_val = Inv561
	   /\ Inv562_val = Inv562
	   /\ Inv563_val = Inv563
	   /\ Inv564_val = Inv564
	   /\ Inv565_val = Inv565
	   /\ Inv566_val = Inv566
	   /\ Inv567_val = Inv567
	   /\ Inv568_val = Inv568
	   /\ Inv569_val = Inv569
	   /\ Inv57_val = Inv57
	   /\ Inv570_val = Inv570
	   /\ Inv571_val = Inv571
	   /\ Inv572_val = Inv572
	   /\ Inv573_val = Inv573
	   /\ Inv574_val = Inv574
	   /\ Inv575_val = Inv575
	   /\ Inv576_val = Inv576
	   /\ Inv577_val = Inv577
	   /\ Inv578_val = Inv578
	   /\ Inv579_val = Inv579
	   /\ Inv58_val = Inv58
	   /\ Inv580_val = Inv580
	   /\ Inv581_val = Inv581
	   /\ Inv582_val = Inv582
	   /\ Inv583_val = Inv583
	   /\ Inv584_val = Inv584
	   /\ Inv585_val = Inv585
	   /\ Inv586_val = Inv586
	   /\ Inv587_val = Inv587
	   /\ Inv588_val = Inv588
	   /\ Inv589_val = Inv589
	   /\ Inv59_val = Inv59
	   /\ Inv590_val = Inv590
	   /\ Inv591_val = Inv591
	   /\ Inv592_val = Inv592
	   /\ Inv593_val = Inv593
	   /\ Inv594_val = Inv594
	   /\ Inv595_val = Inv595
	   /\ Inv596_val = Inv596
	   /\ Inv597_val = Inv597
	   /\ Inv598_val = Inv598
	   /\ Inv599_val = Inv599
	   /\ Inv6_val = Inv6
	   /\ Inv60_val = Inv60
	   /\ Inv600_val = Inv600
	   /\ Inv601_val = Inv601
	   /\ Inv602_val = Inv602
	   /\ Inv603_val = Inv603
	   /\ Inv604_val = Inv604
	   /\ Inv605_val = Inv605
	   /\ Inv606_val = Inv606
	   /\ Inv607_val = Inv607
	   /\ Inv608_val = Inv608
	   /\ Inv609_val = Inv609
	   /\ Inv61_val = Inv61
	   /\ Inv610_val = Inv610
	   /\ Inv611_val = Inv611
	   /\ Inv612_val = Inv612
	   /\ Inv613_val = Inv613
	   /\ Inv614_val = Inv614
	   /\ Inv615_val = Inv615
	   /\ Inv616_val = Inv616
	   /\ Inv617_val = Inv617
	   /\ Inv618_val = Inv618
	   /\ Inv619_val = Inv619
	   /\ Inv62_val = Inv62
	   /\ Inv620_val = Inv620
	   /\ Inv621_val = Inv621
	   /\ Inv622_val = Inv622
	   /\ Inv623_val = Inv623
	   /\ Inv624_val = Inv624
	   /\ Inv625_val = Inv625
	   /\ Inv626_val = Inv626
	   /\ Inv627_val = Inv627
	   /\ Inv628_val = Inv628
	   /\ Inv629_val = Inv629
	   /\ Inv63_val = Inv63
	   /\ Inv630_val = Inv630
	   /\ Inv631_val = Inv631
	   /\ Inv632_val = Inv632
	   /\ Inv633_val = Inv633
	   /\ Inv634_val = Inv634
	   /\ Inv635_val = Inv635
	   /\ Inv636_val = Inv636
	   /\ Inv637_val = Inv637
	   /\ Inv638_val = Inv638
	   /\ Inv639_val = Inv639
	   /\ Inv64_val = Inv64
	   /\ Inv640_val = Inv640
	   /\ Inv641_val = Inv641
	   /\ Inv642_val = Inv642
	   /\ Inv643_val = Inv643
	   /\ Inv644_val = Inv644
	   /\ Inv645_val = Inv645
	   /\ Inv646_val = Inv646
	   /\ Inv647_val = Inv647
	   /\ Inv648_val = Inv648
	   /\ Inv649_val = Inv649
	   /\ Inv65_val = Inv65
	   /\ Inv650_val = Inv650
	   /\ Inv651_val = Inv651
	   /\ Inv652_val = Inv652
	   /\ Inv653_val = Inv653
	   /\ Inv654_val = Inv654
	   /\ Inv655_val = Inv655
	   /\ Inv656_val = Inv656
	   /\ Inv657_val = Inv657
	   /\ Inv658_val = Inv658
	   /\ Inv659_val = Inv659
	   /\ Inv66_val = Inv66
	   /\ Inv660_val = Inv660
	   /\ Inv661_val = Inv661
	   /\ Inv662_val = Inv662
	   /\ Inv663_val = Inv663
	   /\ Inv664_val = Inv664
	   /\ Inv665_val = Inv665
	   /\ Inv666_val = Inv666
	   /\ Inv667_val = Inv667
	   /\ Inv668_val = Inv668
	   /\ Inv669_val = Inv669
	   /\ Inv67_val = Inv67
	   /\ Inv670_val = Inv670
	   /\ Inv671_val = Inv671
	   /\ Inv672_val = Inv672
	   /\ Inv673_val = Inv673
	   /\ Inv674_val = Inv674
	   /\ Inv675_val = Inv675
	   /\ Inv676_val = Inv676
	   /\ Inv677_val = Inv677
	   /\ Inv678_val = Inv678
	   /\ Inv679_val = Inv679
	   /\ Inv68_val = Inv68
	   /\ Inv680_val = Inv680
	   /\ Inv681_val = Inv681
	   /\ Inv682_val = Inv682
	   /\ Inv683_val = Inv683
	   /\ Inv684_val = Inv684
	   /\ Inv685_val = Inv685
	   /\ Inv686_val = Inv686
	   /\ Inv687_val = Inv687
	   /\ Inv688_val = Inv688
	   /\ Inv689_val = Inv689
	   /\ Inv69_val = Inv69
	   /\ Inv690_val = Inv690
	   /\ Inv691_val = Inv691
	   /\ Inv692_val = Inv692
	   /\ Inv693_val = Inv693
	   /\ Inv694_val = Inv694
	   /\ Inv695_val = Inv695
	   /\ Inv696_val = Inv696
	   /\ Inv697_val = Inv697
	   /\ Inv698_val = Inv698
	   /\ Inv699_val = Inv699
	   /\ Inv7_val = Inv7
	   /\ Inv70_val = Inv70
	   /\ Inv700_val = Inv700
	   /\ Inv701_val = Inv701
	   /\ Inv702_val = Inv702
	   /\ Inv703_val = Inv703
	   /\ Inv704_val = Inv704
	   /\ Inv705_val = Inv705
	   /\ Inv706_val = Inv706
	   /\ Inv707_val = Inv707
	   /\ Inv708_val = Inv708
	   /\ Inv709_val = Inv709
	   /\ Inv71_val = Inv71
	   /\ Inv710_val = Inv710
	   /\ Inv711_val = Inv711
	   /\ Inv712_val = Inv712
	   /\ Inv713_val = Inv713
	   /\ Inv714_val = Inv714
	   /\ Inv715_val = Inv715
	   /\ Inv716_val = Inv716
	   /\ Inv717_val = Inv717
	   /\ Inv718_val = Inv718
	   /\ Inv719_val = Inv719
	   /\ Inv72_val = Inv72
	   /\ Inv720_val = Inv720
	   /\ Inv721_val = Inv721
	   /\ Inv722_val = Inv722
	   /\ Inv723_val = Inv723
	   /\ Inv724_val = Inv724
	   /\ Inv725_val = Inv725
	   /\ Inv726_val = Inv726
	   /\ Inv727_val = Inv727
	   /\ Inv728_val = Inv728
	   /\ Inv729_val = Inv729
	   /\ Inv73_val = Inv73
	   /\ Inv730_val = Inv730
	   /\ Inv731_val = Inv731
	   /\ Inv732_val = Inv732
	   /\ Inv733_val = Inv733
	   /\ Inv734_val = Inv734
	   /\ Inv735_val = Inv735
	   /\ Inv736_val = Inv736
	   /\ Inv737_val = Inv737
	   /\ Inv738_val = Inv738
	   /\ Inv739_val = Inv739
	   /\ Inv74_val = Inv74
	   /\ Inv740_val = Inv740
	   /\ Inv741_val = Inv741
	   /\ Inv742_val = Inv742
	   /\ Inv743_val = Inv743
	   /\ Inv744_val = Inv744
	   /\ Inv745_val = Inv745
	   /\ Inv746_val = Inv746
	   /\ Inv747_val = Inv747
	   /\ Inv748_val = Inv748
	   /\ Inv749_val = Inv749
	   /\ Inv75_val = Inv75
	   /\ Inv750_val = Inv750
	   /\ Inv751_val = Inv751
	   /\ Inv752_val = Inv752
	   /\ Inv753_val = Inv753
	   /\ Inv754_val = Inv754
	   /\ Inv755_val = Inv755
	   /\ Inv756_val = Inv756
	   /\ Inv757_val = Inv757
	   /\ Inv758_val = Inv758
	   /\ Inv759_val = Inv759
	   /\ Inv76_val = Inv76
	   /\ Inv77_val = Inv77
	   /\ Inv78_val = Inv78
	   /\ Inv79_val = Inv79
	   /\ Inv8_val = Inv8
	   /\ Inv80_val = Inv80
	   /\ Inv81_val = Inv81
	   /\ Inv82_val = Inv82
	   /\ Inv83_val = Inv83
	   /\ Inv84_val = Inv84
	   /\ Inv85_val = Inv85
	   /\ Inv86_val = Inv86
	   /\ Inv87_val = Inv87
	   /\ Inv88_val = Inv88
	   /\ Inv89_val = Inv89
	   /\ Inv9_val = Inv9
	   /\ Inv90_val = Inv90
	   /\ Inv91_val = Inv91
	   /\ Inv92_val = Inv92
	   /\ Inv93_val = Inv93
	   /\ Inv94_val = Inv94
	   /\ Inv95_val = Inv95
	   /\ Inv96_val = Inv96
	   /\ Inv97_val = Inv97
	   /\ Inv98_val = Inv98
	   /\ Inv99_val = Inv99

CTICheckInit ==
    /\ kCTIs
    /\ InvVals

CTICheckNext ==
    /\ NextUnchanged
    /\ UNCHANGED ctiId
    /\ UNCHANGED Inv0_val
    /\ UNCHANGED Inv1_val
    /\ UNCHANGED Inv10_val
    /\ UNCHANGED Inv100_val
    /\ UNCHANGED Inv101_val
    /\ UNCHANGED Inv102_val
    /\ UNCHANGED Inv103_val
    /\ UNCHANGED Inv104_val
    /\ UNCHANGED Inv105_val
    /\ UNCHANGED Inv106_val
    /\ UNCHANGED Inv107_val
    /\ UNCHANGED Inv108_val
    /\ UNCHANGED Inv109_val
    /\ UNCHANGED Inv11_val
    /\ UNCHANGED Inv110_val
    /\ UNCHANGED Inv111_val
    /\ UNCHANGED Inv112_val
    /\ UNCHANGED Inv113_val
    /\ UNCHANGED Inv114_val
    /\ UNCHANGED Inv115_val
    /\ UNCHANGED Inv116_val
    /\ UNCHANGED Inv117_val
    /\ UNCHANGED Inv118_val
    /\ UNCHANGED Inv119_val
    /\ UNCHANGED Inv12_val
    /\ UNCHANGED Inv120_val
    /\ UNCHANGED Inv121_val
    /\ UNCHANGED Inv122_val
    /\ UNCHANGED Inv123_val
    /\ UNCHANGED Inv124_val
    /\ UNCHANGED Inv125_val
    /\ UNCHANGED Inv126_val
    /\ UNCHANGED Inv127_val
    /\ UNCHANGED Inv128_val
    /\ UNCHANGED Inv129_val
    /\ UNCHANGED Inv13_val
    /\ UNCHANGED Inv130_val
    /\ UNCHANGED Inv131_val
    /\ UNCHANGED Inv132_val
    /\ UNCHANGED Inv133_val
    /\ UNCHANGED Inv134_val
    /\ UNCHANGED Inv135_val
    /\ UNCHANGED Inv136_val
    /\ UNCHANGED Inv137_val
    /\ UNCHANGED Inv138_val
    /\ UNCHANGED Inv139_val
    /\ UNCHANGED Inv14_val
    /\ UNCHANGED Inv140_val
    /\ UNCHANGED Inv141_val
    /\ UNCHANGED Inv142_val
    /\ UNCHANGED Inv143_val
    /\ UNCHANGED Inv144_val
    /\ UNCHANGED Inv145_val
    /\ UNCHANGED Inv146_val
    /\ UNCHANGED Inv147_val
    /\ UNCHANGED Inv148_val
    /\ UNCHANGED Inv149_val
    /\ UNCHANGED Inv15_val
    /\ UNCHANGED Inv150_val
    /\ UNCHANGED Inv151_val
    /\ UNCHANGED Inv152_val
    /\ UNCHANGED Inv153_val
    /\ UNCHANGED Inv154_val
    /\ UNCHANGED Inv155_val
    /\ UNCHANGED Inv156_val
    /\ UNCHANGED Inv157_val
    /\ UNCHANGED Inv158_val
    /\ UNCHANGED Inv159_val
    /\ UNCHANGED Inv16_val
    /\ UNCHANGED Inv160_val
    /\ UNCHANGED Inv161_val
    /\ UNCHANGED Inv162_val
    /\ UNCHANGED Inv163_val
    /\ UNCHANGED Inv164_val
    /\ UNCHANGED Inv165_val
    /\ UNCHANGED Inv166_val
    /\ UNCHANGED Inv167_val
    /\ UNCHANGED Inv168_val
    /\ UNCHANGED Inv169_val
    /\ UNCHANGED Inv17_val
    /\ UNCHANGED Inv170_val
    /\ UNCHANGED Inv171_val
    /\ UNCHANGED Inv172_val
    /\ UNCHANGED Inv173_val
    /\ UNCHANGED Inv174_val
    /\ UNCHANGED Inv175_val
    /\ UNCHANGED Inv176_val
    /\ UNCHANGED Inv177_val
    /\ UNCHANGED Inv178_val
    /\ UNCHANGED Inv179_val
    /\ UNCHANGED Inv18_val
    /\ UNCHANGED Inv180_val
    /\ UNCHANGED Inv181_val
    /\ UNCHANGED Inv182_val
    /\ UNCHANGED Inv183_val
    /\ UNCHANGED Inv184_val
    /\ UNCHANGED Inv185_val
    /\ UNCHANGED Inv186_val
    /\ UNCHANGED Inv187_val
    /\ UNCHANGED Inv188_val
    /\ UNCHANGED Inv189_val
    /\ UNCHANGED Inv19_val
    /\ UNCHANGED Inv190_val
    /\ UNCHANGED Inv191_val
    /\ UNCHANGED Inv192_val
    /\ UNCHANGED Inv193_val
    /\ UNCHANGED Inv194_val
    /\ UNCHANGED Inv195_val
    /\ UNCHANGED Inv196_val
    /\ UNCHANGED Inv197_val
    /\ UNCHANGED Inv198_val
    /\ UNCHANGED Inv199_val
    /\ UNCHANGED Inv2_val
    /\ UNCHANGED Inv20_val
    /\ UNCHANGED Inv200_val
    /\ UNCHANGED Inv201_val
    /\ UNCHANGED Inv202_val
    /\ UNCHANGED Inv203_val
    /\ UNCHANGED Inv204_val
    /\ UNCHANGED Inv205_val
    /\ UNCHANGED Inv206_val
    /\ UNCHANGED Inv207_val
    /\ UNCHANGED Inv208_val
    /\ UNCHANGED Inv209_val
    /\ UNCHANGED Inv21_val
    /\ UNCHANGED Inv210_val
    /\ UNCHANGED Inv211_val
    /\ UNCHANGED Inv212_val
    /\ UNCHANGED Inv213_val
    /\ UNCHANGED Inv214_val
    /\ UNCHANGED Inv215_val
    /\ UNCHANGED Inv216_val
    /\ UNCHANGED Inv217_val
    /\ UNCHANGED Inv218_val
    /\ UNCHANGED Inv219_val
    /\ UNCHANGED Inv22_val
    /\ UNCHANGED Inv220_val
    /\ UNCHANGED Inv221_val
    /\ UNCHANGED Inv222_val
    /\ UNCHANGED Inv223_val
    /\ UNCHANGED Inv224_val
    /\ UNCHANGED Inv225_val
    /\ UNCHANGED Inv226_val
    /\ UNCHANGED Inv227_val
    /\ UNCHANGED Inv228_val
    /\ UNCHANGED Inv229_val
    /\ UNCHANGED Inv23_val
    /\ UNCHANGED Inv230_val
    /\ UNCHANGED Inv231_val
    /\ UNCHANGED Inv232_val
    /\ UNCHANGED Inv233_val
    /\ UNCHANGED Inv234_val
    /\ UNCHANGED Inv235_val
    /\ UNCHANGED Inv236_val
    /\ UNCHANGED Inv237_val
    /\ UNCHANGED Inv238_val
    /\ UNCHANGED Inv239_val
    /\ UNCHANGED Inv24_val
    /\ UNCHANGED Inv240_val
    /\ UNCHANGED Inv241_val
    /\ UNCHANGED Inv242_val
    /\ UNCHANGED Inv243_val
    /\ UNCHANGED Inv244_val
    /\ UNCHANGED Inv245_val
    /\ UNCHANGED Inv246_val
    /\ UNCHANGED Inv247_val
    /\ UNCHANGED Inv248_val
    /\ UNCHANGED Inv249_val
    /\ UNCHANGED Inv25_val
    /\ UNCHANGED Inv250_val
    /\ UNCHANGED Inv251_val
    /\ UNCHANGED Inv252_val
    /\ UNCHANGED Inv253_val
    /\ UNCHANGED Inv254_val
    /\ UNCHANGED Inv255_val
    /\ UNCHANGED Inv256_val
    /\ UNCHANGED Inv257_val
    /\ UNCHANGED Inv258_val
    /\ UNCHANGED Inv259_val
    /\ UNCHANGED Inv26_val
    /\ UNCHANGED Inv260_val
    /\ UNCHANGED Inv261_val
    /\ UNCHANGED Inv262_val
    /\ UNCHANGED Inv263_val
    /\ UNCHANGED Inv264_val
    /\ UNCHANGED Inv265_val
    /\ UNCHANGED Inv266_val
    /\ UNCHANGED Inv267_val
    /\ UNCHANGED Inv268_val
    /\ UNCHANGED Inv269_val
    /\ UNCHANGED Inv27_val
    /\ UNCHANGED Inv270_val
    /\ UNCHANGED Inv271_val
    /\ UNCHANGED Inv272_val
    /\ UNCHANGED Inv273_val
    /\ UNCHANGED Inv274_val
    /\ UNCHANGED Inv275_val
    /\ UNCHANGED Inv276_val
    /\ UNCHANGED Inv277_val
    /\ UNCHANGED Inv278_val
    /\ UNCHANGED Inv279_val
    /\ UNCHANGED Inv28_val
    /\ UNCHANGED Inv280_val
    /\ UNCHANGED Inv281_val
    /\ UNCHANGED Inv282_val
    /\ UNCHANGED Inv283_val
    /\ UNCHANGED Inv284_val
    /\ UNCHANGED Inv285_val
    /\ UNCHANGED Inv286_val
    /\ UNCHANGED Inv287_val
    /\ UNCHANGED Inv288_val
    /\ UNCHANGED Inv289_val
    /\ UNCHANGED Inv29_val
    /\ UNCHANGED Inv290_val
    /\ UNCHANGED Inv291_val
    /\ UNCHANGED Inv292_val
    /\ UNCHANGED Inv293_val
    /\ UNCHANGED Inv294_val
    /\ UNCHANGED Inv295_val
    /\ UNCHANGED Inv296_val
    /\ UNCHANGED Inv297_val
    /\ UNCHANGED Inv298_val
    /\ UNCHANGED Inv299_val
    /\ UNCHANGED Inv3_val
    /\ UNCHANGED Inv30_val
    /\ UNCHANGED Inv300_val
    /\ UNCHANGED Inv301_val
    /\ UNCHANGED Inv302_val
    /\ UNCHANGED Inv303_val
    /\ UNCHANGED Inv304_val
    /\ UNCHANGED Inv305_val
    /\ UNCHANGED Inv306_val
    /\ UNCHANGED Inv307_val
    /\ UNCHANGED Inv308_val
    /\ UNCHANGED Inv309_val
    /\ UNCHANGED Inv31_val
    /\ UNCHANGED Inv310_val
    /\ UNCHANGED Inv311_val
    /\ UNCHANGED Inv312_val
    /\ UNCHANGED Inv313_val
    /\ UNCHANGED Inv314_val
    /\ UNCHANGED Inv315_val
    /\ UNCHANGED Inv316_val
    /\ UNCHANGED Inv317_val
    /\ UNCHANGED Inv318_val
    /\ UNCHANGED Inv319_val
    /\ UNCHANGED Inv32_val
    /\ UNCHANGED Inv320_val
    /\ UNCHANGED Inv321_val
    /\ UNCHANGED Inv322_val
    /\ UNCHANGED Inv323_val
    /\ UNCHANGED Inv324_val
    /\ UNCHANGED Inv325_val
    /\ UNCHANGED Inv326_val
    /\ UNCHANGED Inv327_val
    /\ UNCHANGED Inv328_val
    /\ UNCHANGED Inv329_val
    /\ UNCHANGED Inv33_val
    /\ UNCHANGED Inv330_val
    /\ UNCHANGED Inv331_val
    /\ UNCHANGED Inv332_val
    /\ UNCHANGED Inv333_val
    /\ UNCHANGED Inv334_val
    /\ UNCHANGED Inv335_val
    /\ UNCHANGED Inv336_val
    /\ UNCHANGED Inv337_val
    /\ UNCHANGED Inv338_val
    /\ UNCHANGED Inv339_val
    /\ UNCHANGED Inv34_val
    /\ UNCHANGED Inv340_val
    /\ UNCHANGED Inv341_val
    /\ UNCHANGED Inv342_val
    /\ UNCHANGED Inv343_val
    /\ UNCHANGED Inv344_val
    /\ UNCHANGED Inv345_val
    /\ UNCHANGED Inv346_val
    /\ UNCHANGED Inv347_val
    /\ UNCHANGED Inv348_val
    /\ UNCHANGED Inv349_val
    /\ UNCHANGED Inv35_val
    /\ UNCHANGED Inv350_val
    /\ UNCHANGED Inv351_val
    /\ UNCHANGED Inv352_val
    /\ UNCHANGED Inv353_val
    /\ UNCHANGED Inv354_val
    /\ UNCHANGED Inv355_val
    /\ UNCHANGED Inv356_val
    /\ UNCHANGED Inv357_val
    /\ UNCHANGED Inv358_val
    /\ UNCHANGED Inv359_val
    /\ UNCHANGED Inv36_val
    /\ UNCHANGED Inv360_val
    /\ UNCHANGED Inv361_val
    /\ UNCHANGED Inv362_val
    /\ UNCHANGED Inv363_val
    /\ UNCHANGED Inv364_val
    /\ UNCHANGED Inv365_val
    /\ UNCHANGED Inv366_val
    /\ UNCHANGED Inv367_val
    /\ UNCHANGED Inv368_val
    /\ UNCHANGED Inv369_val
    /\ UNCHANGED Inv37_val
    /\ UNCHANGED Inv370_val
    /\ UNCHANGED Inv371_val
    /\ UNCHANGED Inv372_val
    /\ UNCHANGED Inv373_val
    /\ UNCHANGED Inv374_val
    /\ UNCHANGED Inv375_val
    /\ UNCHANGED Inv376_val
    /\ UNCHANGED Inv377_val
    /\ UNCHANGED Inv378_val
    /\ UNCHANGED Inv379_val
    /\ UNCHANGED Inv38_val
    /\ UNCHANGED Inv380_val
    /\ UNCHANGED Inv381_val
    /\ UNCHANGED Inv382_val
    /\ UNCHANGED Inv383_val
    /\ UNCHANGED Inv384_val
    /\ UNCHANGED Inv385_val
    /\ UNCHANGED Inv386_val
    /\ UNCHANGED Inv387_val
    /\ UNCHANGED Inv388_val
    /\ UNCHANGED Inv389_val
    /\ UNCHANGED Inv39_val
    /\ UNCHANGED Inv390_val
    /\ UNCHANGED Inv391_val
    /\ UNCHANGED Inv392_val
    /\ UNCHANGED Inv393_val
    /\ UNCHANGED Inv394_val
    /\ UNCHANGED Inv395_val
    /\ UNCHANGED Inv396_val
    /\ UNCHANGED Inv397_val
    /\ UNCHANGED Inv398_val
    /\ UNCHANGED Inv399_val
    /\ UNCHANGED Inv4_val
    /\ UNCHANGED Inv40_val
    /\ UNCHANGED Inv400_val
    /\ UNCHANGED Inv401_val
    /\ UNCHANGED Inv402_val
    /\ UNCHANGED Inv403_val
    /\ UNCHANGED Inv404_val
    /\ UNCHANGED Inv405_val
    /\ UNCHANGED Inv406_val
    /\ UNCHANGED Inv407_val
    /\ UNCHANGED Inv408_val
    /\ UNCHANGED Inv409_val
    /\ UNCHANGED Inv41_val
    /\ UNCHANGED Inv410_val
    /\ UNCHANGED Inv411_val
    /\ UNCHANGED Inv412_val
    /\ UNCHANGED Inv413_val
    /\ UNCHANGED Inv414_val
    /\ UNCHANGED Inv415_val
    /\ UNCHANGED Inv416_val
    /\ UNCHANGED Inv417_val
    /\ UNCHANGED Inv418_val
    /\ UNCHANGED Inv419_val
    /\ UNCHANGED Inv42_val
    /\ UNCHANGED Inv420_val
    /\ UNCHANGED Inv421_val
    /\ UNCHANGED Inv422_val
    /\ UNCHANGED Inv423_val
    /\ UNCHANGED Inv424_val
    /\ UNCHANGED Inv425_val
    /\ UNCHANGED Inv426_val
    /\ UNCHANGED Inv427_val
    /\ UNCHANGED Inv428_val
    /\ UNCHANGED Inv429_val
    /\ UNCHANGED Inv43_val
    /\ UNCHANGED Inv430_val
    /\ UNCHANGED Inv431_val
    /\ UNCHANGED Inv432_val
    /\ UNCHANGED Inv433_val
    /\ UNCHANGED Inv434_val
    /\ UNCHANGED Inv435_val
    /\ UNCHANGED Inv436_val
    /\ UNCHANGED Inv437_val
    /\ UNCHANGED Inv438_val
    /\ UNCHANGED Inv439_val
    /\ UNCHANGED Inv44_val
    /\ UNCHANGED Inv440_val
    /\ UNCHANGED Inv441_val
    /\ UNCHANGED Inv442_val
    /\ UNCHANGED Inv443_val
    /\ UNCHANGED Inv444_val
    /\ UNCHANGED Inv445_val
    /\ UNCHANGED Inv446_val
    /\ UNCHANGED Inv447_val
    /\ UNCHANGED Inv448_val
    /\ UNCHANGED Inv449_val
    /\ UNCHANGED Inv45_val
    /\ UNCHANGED Inv450_val
    /\ UNCHANGED Inv451_val
    /\ UNCHANGED Inv452_val
    /\ UNCHANGED Inv453_val
    /\ UNCHANGED Inv454_val
    /\ UNCHANGED Inv455_val
    /\ UNCHANGED Inv456_val
    /\ UNCHANGED Inv457_val
    /\ UNCHANGED Inv458_val
    /\ UNCHANGED Inv459_val
    /\ UNCHANGED Inv46_val
    /\ UNCHANGED Inv460_val
    /\ UNCHANGED Inv461_val
    /\ UNCHANGED Inv462_val
    /\ UNCHANGED Inv463_val
    /\ UNCHANGED Inv464_val
    /\ UNCHANGED Inv465_val
    /\ UNCHANGED Inv466_val
    /\ UNCHANGED Inv467_val
    /\ UNCHANGED Inv468_val
    /\ UNCHANGED Inv469_val
    /\ UNCHANGED Inv47_val
    /\ UNCHANGED Inv470_val
    /\ UNCHANGED Inv471_val
    /\ UNCHANGED Inv472_val
    /\ UNCHANGED Inv473_val
    /\ UNCHANGED Inv474_val
    /\ UNCHANGED Inv475_val
    /\ UNCHANGED Inv476_val
    /\ UNCHANGED Inv477_val
    /\ UNCHANGED Inv478_val
    /\ UNCHANGED Inv479_val
    /\ UNCHANGED Inv48_val
    /\ UNCHANGED Inv480_val
    /\ UNCHANGED Inv481_val
    /\ UNCHANGED Inv482_val
    /\ UNCHANGED Inv483_val
    /\ UNCHANGED Inv484_val
    /\ UNCHANGED Inv485_val
    /\ UNCHANGED Inv486_val
    /\ UNCHANGED Inv487_val
    /\ UNCHANGED Inv488_val
    /\ UNCHANGED Inv489_val
    /\ UNCHANGED Inv49_val
    /\ UNCHANGED Inv490_val
    /\ UNCHANGED Inv491_val
    /\ UNCHANGED Inv492_val
    /\ UNCHANGED Inv493_val
    /\ UNCHANGED Inv494_val
    /\ UNCHANGED Inv495_val
    /\ UNCHANGED Inv496_val
    /\ UNCHANGED Inv497_val
    /\ UNCHANGED Inv498_val
    /\ UNCHANGED Inv499_val
    /\ UNCHANGED Inv5_val
    /\ UNCHANGED Inv50_val
    /\ UNCHANGED Inv500_val
    /\ UNCHANGED Inv501_val
    /\ UNCHANGED Inv502_val
    /\ UNCHANGED Inv503_val
    /\ UNCHANGED Inv504_val
    /\ UNCHANGED Inv505_val
    /\ UNCHANGED Inv506_val
    /\ UNCHANGED Inv507_val
    /\ UNCHANGED Inv508_val
    /\ UNCHANGED Inv509_val
    /\ UNCHANGED Inv51_val
    /\ UNCHANGED Inv510_val
    /\ UNCHANGED Inv511_val
    /\ UNCHANGED Inv512_val
    /\ UNCHANGED Inv513_val
    /\ UNCHANGED Inv514_val
    /\ UNCHANGED Inv515_val
    /\ UNCHANGED Inv516_val
    /\ UNCHANGED Inv517_val
    /\ UNCHANGED Inv518_val
    /\ UNCHANGED Inv519_val
    /\ UNCHANGED Inv52_val
    /\ UNCHANGED Inv520_val
    /\ UNCHANGED Inv521_val
    /\ UNCHANGED Inv522_val
    /\ UNCHANGED Inv523_val
    /\ UNCHANGED Inv524_val
    /\ UNCHANGED Inv525_val
    /\ UNCHANGED Inv526_val
    /\ UNCHANGED Inv527_val
    /\ UNCHANGED Inv528_val
    /\ UNCHANGED Inv529_val
    /\ UNCHANGED Inv53_val
    /\ UNCHANGED Inv530_val
    /\ UNCHANGED Inv531_val
    /\ UNCHANGED Inv532_val
    /\ UNCHANGED Inv533_val
    /\ UNCHANGED Inv534_val
    /\ UNCHANGED Inv535_val
    /\ UNCHANGED Inv536_val
    /\ UNCHANGED Inv537_val
    /\ UNCHANGED Inv538_val
    /\ UNCHANGED Inv539_val
    /\ UNCHANGED Inv54_val
    /\ UNCHANGED Inv540_val
    /\ UNCHANGED Inv541_val
    /\ UNCHANGED Inv542_val
    /\ UNCHANGED Inv543_val
    /\ UNCHANGED Inv544_val
    /\ UNCHANGED Inv545_val
    /\ UNCHANGED Inv546_val
    /\ UNCHANGED Inv547_val
    /\ UNCHANGED Inv548_val
    /\ UNCHANGED Inv549_val
    /\ UNCHANGED Inv55_val
    /\ UNCHANGED Inv550_val
    /\ UNCHANGED Inv551_val
    /\ UNCHANGED Inv552_val
    /\ UNCHANGED Inv553_val
    /\ UNCHANGED Inv554_val
    /\ UNCHANGED Inv555_val
    /\ UNCHANGED Inv556_val
    /\ UNCHANGED Inv557_val
    /\ UNCHANGED Inv558_val
    /\ UNCHANGED Inv559_val
    /\ UNCHANGED Inv56_val
    /\ UNCHANGED Inv560_val
    /\ UNCHANGED Inv561_val
    /\ UNCHANGED Inv562_val
    /\ UNCHANGED Inv563_val
    /\ UNCHANGED Inv564_val
    /\ UNCHANGED Inv565_val
    /\ UNCHANGED Inv566_val
    /\ UNCHANGED Inv567_val
    /\ UNCHANGED Inv568_val
    /\ UNCHANGED Inv569_val
    /\ UNCHANGED Inv57_val
    /\ UNCHANGED Inv570_val
    /\ UNCHANGED Inv571_val
    /\ UNCHANGED Inv572_val
    /\ UNCHANGED Inv573_val
    /\ UNCHANGED Inv574_val
    /\ UNCHANGED Inv575_val
    /\ UNCHANGED Inv576_val
    /\ UNCHANGED Inv577_val
    /\ UNCHANGED Inv578_val
    /\ UNCHANGED Inv579_val
    /\ UNCHANGED Inv58_val
    /\ UNCHANGED Inv580_val
    /\ UNCHANGED Inv581_val
    /\ UNCHANGED Inv582_val
    /\ UNCHANGED Inv583_val
    /\ UNCHANGED Inv584_val
    /\ UNCHANGED Inv585_val
    /\ UNCHANGED Inv586_val
    /\ UNCHANGED Inv587_val
    /\ UNCHANGED Inv588_val
    /\ UNCHANGED Inv589_val
    /\ UNCHANGED Inv59_val
    /\ UNCHANGED Inv590_val
    /\ UNCHANGED Inv591_val
    /\ UNCHANGED Inv592_val
    /\ UNCHANGED Inv593_val
    /\ UNCHANGED Inv594_val
    /\ UNCHANGED Inv595_val
    /\ UNCHANGED Inv596_val
    /\ UNCHANGED Inv597_val
    /\ UNCHANGED Inv598_val
    /\ UNCHANGED Inv599_val
    /\ UNCHANGED Inv6_val
    /\ UNCHANGED Inv60_val
    /\ UNCHANGED Inv600_val
    /\ UNCHANGED Inv601_val
    /\ UNCHANGED Inv602_val
    /\ UNCHANGED Inv603_val
    /\ UNCHANGED Inv604_val
    /\ UNCHANGED Inv605_val
    /\ UNCHANGED Inv606_val
    /\ UNCHANGED Inv607_val
    /\ UNCHANGED Inv608_val
    /\ UNCHANGED Inv609_val
    /\ UNCHANGED Inv61_val
    /\ UNCHANGED Inv610_val
    /\ UNCHANGED Inv611_val
    /\ UNCHANGED Inv612_val
    /\ UNCHANGED Inv613_val
    /\ UNCHANGED Inv614_val
    /\ UNCHANGED Inv615_val
    /\ UNCHANGED Inv616_val
    /\ UNCHANGED Inv617_val
    /\ UNCHANGED Inv618_val
    /\ UNCHANGED Inv619_val
    /\ UNCHANGED Inv62_val
    /\ UNCHANGED Inv620_val
    /\ UNCHANGED Inv621_val
    /\ UNCHANGED Inv622_val
    /\ UNCHANGED Inv623_val
    /\ UNCHANGED Inv624_val
    /\ UNCHANGED Inv625_val
    /\ UNCHANGED Inv626_val
    /\ UNCHANGED Inv627_val
    /\ UNCHANGED Inv628_val
    /\ UNCHANGED Inv629_val
    /\ UNCHANGED Inv63_val
    /\ UNCHANGED Inv630_val
    /\ UNCHANGED Inv631_val
    /\ UNCHANGED Inv632_val
    /\ UNCHANGED Inv633_val
    /\ UNCHANGED Inv634_val
    /\ UNCHANGED Inv635_val
    /\ UNCHANGED Inv636_val
    /\ UNCHANGED Inv637_val
    /\ UNCHANGED Inv638_val
    /\ UNCHANGED Inv639_val
    /\ UNCHANGED Inv64_val
    /\ UNCHANGED Inv640_val
    /\ UNCHANGED Inv641_val
    /\ UNCHANGED Inv642_val
    /\ UNCHANGED Inv643_val
    /\ UNCHANGED Inv644_val
    /\ UNCHANGED Inv645_val
    /\ UNCHANGED Inv646_val
    /\ UNCHANGED Inv647_val
    /\ UNCHANGED Inv648_val
    /\ UNCHANGED Inv649_val
    /\ UNCHANGED Inv65_val
    /\ UNCHANGED Inv650_val
    /\ UNCHANGED Inv651_val
    /\ UNCHANGED Inv652_val
    /\ UNCHANGED Inv653_val
    /\ UNCHANGED Inv654_val
    /\ UNCHANGED Inv655_val
    /\ UNCHANGED Inv656_val
    /\ UNCHANGED Inv657_val
    /\ UNCHANGED Inv658_val
    /\ UNCHANGED Inv659_val
    /\ UNCHANGED Inv66_val
    /\ UNCHANGED Inv660_val
    /\ UNCHANGED Inv661_val
    /\ UNCHANGED Inv662_val
    /\ UNCHANGED Inv663_val
    /\ UNCHANGED Inv664_val
    /\ UNCHANGED Inv665_val
    /\ UNCHANGED Inv666_val
    /\ UNCHANGED Inv667_val
    /\ UNCHANGED Inv668_val
    /\ UNCHANGED Inv669_val
    /\ UNCHANGED Inv67_val
    /\ UNCHANGED Inv670_val
    /\ UNCHANGED Inv671_val
    /\ UNCHANGED Inv672_val
    /\ UNCHANGED Inv673_val
    /\ UNCHANGED Inv674_val
    /\ UNCHANGED Inv675_val
    /\ UNCHANGED Inv676_val
    /\ UNCHANGED Inv677_val
    /\ UNCHANGED Inv678_val
    /\ UNCHANGED Inv679_val
    /\ UNCHANGED Inv68_val
    /\ UNCHANGED Inv680_val
    /\ UNCHANGED Inv681_val
    /\ UNCHANGED Inv682_val
    /\ UNCHANGED Inv683_val
    /\ UNCHANGED Inv684_val
    /\ UNCHANGED Inv685_val
    /\ UNCHANGED Inv686_val
    /\ UNCHANGED Inv687_val
    /\ UNCHANGED Inv688_val
    /\ UNCHANGED Inv689_val
    /\ UNCHANGED Inv69_val
    /\ UNCHANGED Inv690_val
    /\ UNCHANGED Inv691_val
    /\ UNCHANGED Inv692_val
    /\ UNCHANGED Inv693_val
    /\ UNCHANGED Inv694_val
    /\ UNCHANGED Inv695_val
    /\ UNCHANGED Inv696_val
    /\ UNCHANGED Inv697_val
    /\ UNCHANGED Inv698_val
    /\ UNCHANGED Inv699_val
    /\ UNCHANGED Inv7_val
    /\ UNCHANGED Inv70_val
    /\ UNCHANGED Inv700_val
    /\ UNCHANGED Inv701_val
    /\ UNCHANGED Inv702_val
    /\ UNCHANGED Inv703_val
    /\ UNCHANGED Inv704_val
    /\ UNCHANGED Inv705_val
    /\ UNCHANGED Inv706_val
    /\ UNCHANGED Inv707_val
    /\ UNCHANGED Inv708_val
    /\ UNCHANGED Inv709_val
    /\ UNCHANGED Inv71_val
    /\ UNCHANGED Inv710_val
    /\ UNCHANGED Inv711_val
    /\ UNCHANGED Inv712_val
    /\ UNCHANGED Inv713_val
    /\ UNCHANGED Inv714_val
    /\ UNCHANGED Inv715_val
    /\ UNCHANGED Inv716_val
    /\ UNCHANGED Inv717_val
    /\ UNCHANGED Inv718_val
    /\ UNCHANGED Inv719_val
    /\ UNCHANGED Inv72_val
    /\ UNCHANGED Inv720_val
    /\ UNCHANGED Inv721_val
    /\ UNCHANGED Inv722_val
    /\ UNCHANGED Inv723_val
    /\ UNCHANGED Inv724_val
    /\ UNCHANGED Inv725_val
    /\ UNCHANGED Inv726_val
    /\ UNCHANGED Inv727_val
    /\ UNCHANGED Inv728_val
    /\ UNCHANGED Inv729_val
    /\ UNCHANGED Inv73_val
    /\ UNCHANGED Inv730_val
    /\ UNCHANGED Inv731_val
    /\ UNCHANGED Inv732_val
    /\ UNCHANGED Inv733_val
    /\ UNCHANGED Inv734_val
    /\ UNCHANGED Inv735_val
    /\ UNCHANGED Inv736_val
    /\ UNCHANGED Inv737_val
    /\ UNCHANGED Inv738_val
    /\ UNCHANGED Inv739_val
    /\ UNCHANGED Inv74_val
    /\ UNCHANGED Inv740_val
    /\ UNCHANGED Inv741_val
    /\ UNCHANGED Inv742_val
    /\ UNCHANGED Inv743_val
    /\ UNCHANGED Inv744_val
    /\ UNCHANGED Inv745_val
    /\ UNCHANGED Inv746_val
    /\ UNCHANGED Inv747_val
    /\ UNCHANGED Inv748_val
    /\ UNCHANGED Inv749_val
    /\ UNCHANGED Inv75_val
    /\ UNCHANGED Inv750_val
    /\ UNCHANGED Inv751_val
    /\ UNCHANGED Inv752_val
    /\ UNCHANGED Inv753_val
    /\ UNCHANGED Inv754_val
    /\ UNCHANGED Inv755_val
    /\ UNCHANGED Inv756_val
    /\ UNCHANGED Inv757_val
    /\ UNCHANGED Inv758_val
    /\ UNCHANGED Inv759_val
    /\ UNCHANGED Inv76_val
    /\ UNCHANGED Inv77_val
    /\ UNCHANGED Inv78_val
    /\ UNCHANGED Inv79_val
    /\ UNCHANGED Inv8_val
    /\ UNCHANGED Inv80_val
    /\ UNCHANGED Inv81_val
    /\ UNCHANGED Inv82_val
    /\ UNCHANGED Inv83_val
    /\ UNCHANGED Inv84_val
    /\ UNCHANGED Inv85_val
    /\ UNCHANGED Inv86_val
    /\ UNCHANGED Inv87_val
    /\ UNCHANGED Inv88_val
    /\ UNCHANGED Inv89_val
    /\ UNCHANGED Inv9_val
    /\ UNCHANGED Inv90_val
    /\ UNCHANGED Inv91_val
    /\ UNCHANGED Inv92_val
    /\ UNCHANGED Inv93_val
    /\ UNCHANGED Inv94_val
    /\ UNCHANGED Inv95_val
    /\ UNCHANGED Inv96_val
    /\ UNCHANGED Inv97_val
    /\ UNCHANGED Inv98_val
    /\ UNCHANGED Inv99_val
====