package org.sonatype.mavenbook.weather.model;

import javax.persistence.*;

@Entity
public class Condition {

  @Id
  @GeneratedValue(strategy=GenerationType.IDENTITY)
  private Integer id;

  private String text;
  private String code;
  private String temp;
  private String date;

  @OneToOne(cascade=CascadeType.ALL)
  @JoinColumn(name="weather_id", nullable=false)
  private Weather weather;

  public Condition() {}

  public Integer getId() { return id; }
  public void setId(Integer id) { this.id = id; }

  public String getText() { return text; }
  public void setText(String text) { this.text = text; }

  public String getCode() { return code; }
  public void setCode(String code) { this.code = code; }

  public String getTemp() { return temp; }
  public void setTemp(String temp) { this.temp = temp; }

  public String getDate() { return date; }
  public void setDate(String date) { this.date = date; }

}
