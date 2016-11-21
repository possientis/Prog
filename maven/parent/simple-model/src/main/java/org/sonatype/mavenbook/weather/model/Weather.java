// Annotated Weather model object
// Using Hibernate annotations

package org.sonatype.mavenbook.weather.model;

import javax.persistence.*;
import java.util.Date;

// query written in HQL (Hibernate Query Language)
// no @Table annotation, so embedded DB table will be 'Weather'
@Entity
@NamedQueries({
@NamedQuery(name="Weather.byLocation",
            query="from Weather w where w.location = :location")
})
public class Weather {
  // @Id marks the class property which contains the primary key in table
  // @GeneratedValue controls how many new primary key values are generated
  @Id
  @GeneratedValue(strategy=GenerationType.IDENTITY)
  private Integer id;

  // @ManyToOne ensures that weather objects which point to the same
  // Location object reference the same instance
  @ManyToOne(cascade=CascadeType.ALL)
  private Location location;

  @OneToOne(mappedBy="weather",cascade=CascadeType.ALL)
  private Condition condition;

  @OneToOne(mappedBy="weather",cascade=CascadeType.ALL)
  private Wind wind;

  @OneToOne(mappedBy="weather",cascade=CascadeType.ALL)
  private Atmosphere atmosphere;

  private Date date;

  public Weather() {}

  public Integer getId() { return id; }
  public void setId(Integer id) { this.id = id; }

  public Location getLocation() { return location; }
  public void setLocation(Location location) { this.location = location; }

  public Condition getCondition() { return condition; }
  public void setCondition(Condition condition) { this.condition = condition; }

  public Wind getWind() { return wind; }
  public void setWind(Wind wind) { this.wind = wind; }

  public Atmosphere getAtmosphere() { return atmosphere; }
  public void setAtmosphere(Atmosphere atmosph) { this.atmosphere = atmosph; }

}




